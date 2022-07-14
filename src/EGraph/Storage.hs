{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
module EGraph.Storage where

import qualified Data.Vector.Unboxed as VU
import qualified Data.IntSet as IS
import qualified Data.IntMap.Strict as M
import qualified Data.HashMap.Strict as HM
import EGraph.UnionFind as UF
import GHC.Generics (Generic)
import Data.Generics.Labels ()
import GHC.Base (build)
import Control.Monad.State.Strict
import Control.Lens
import Data.Hashable
import Optics.Utils
import Control.Monad.Primitive
import qualified Data.Growable as GV
import Data.Mutable.Lens
import Data.Mutable.Indexing
import qualified Data.Vector.Mutable as VB
import qualified Data.Vector.Hashtables as D
import Data.Mutable.Distributive
import Data.Mutable.Each
import Data.Monoid (Any(..))
import Data.Generics.Product.Fields (HasField)
import Control.Monad.Identity (IdentityT)
import qualified Data.Vector as VB
import qualified Data.Set as S
import Debug.Trace (traceM)
import Control.Monad.Writer (WriterT, tell, execWriterT, MonadWriter)
import qualified Data.IntMap.Merge.Strict as MM
import qualified Data.List as L
import GHC.IO (unsafeSTToIO, unsafeDupablePerformIO)
import Control.Monad.ST (runST, ST)
import GHC.Stack (HasCallStack)
import Control.Monad.RWS (MonadReader)

-- TODO: track refcounts of classes, and do incremental reachability checks from some root set
-- This way we can do cheap-ish garbage collection when replacing expressions via CHR
type Id = Int
type SymbolMap = M.IntMap
type Symbol = Int
type ClassMap = M.IntMap
type ClassSet = IS.IntSet
type Row = VU.Vector Int
data AClass = AClass {
    class_id :: !Id,              -- ^ still you, even after everything
    tables :: !(SymbolMap Table), -- ^ One DB Table per class and symbol
    referenced_by :: !ClassSet,    -- ^ Who gets dirty if our id changes
    references :: !ClassSet    -- ^ Who gets dirty if our id changes
} deriving (Eq, Ord, Show, Generic)
type TableContent = VU.Vector Int
data Table = Table {
    row_width :: !Int,
    content :: !TableContent,    -- | Sorted Id[][row_width]
    references  :: !ClassSet     -- | Who do we reference, used to skip normalization
} deriving (Eq, Ord, Show, Generic)

showTable :: Symbol -> Table -> [String]
showTable sym table
  | table.row_width == 0 = [show sym <> "()"]
  | otherwise = [ show sym <> show row  | row <- tableRows table ]

showClass :: AClass -> String
showClass cls
  | M.null cls.tables = show (cls.class_id) <> " = ?\n"
  | otherwise = unlines [ show cls.class_id  <> " = " <> row |(sym,table) <- M.toList cls.tables, row <- showTable sym table ]
showEgg :: EGraph -> String
showEgg eg = concat [ showClass cls | cls <- M.elems eg.classes ]


tableSize :: Table -> Int
tableSize t 
  | t.row_width == 0 = 1
  | otherwise = VU.length t.content `div` t.row_width
tableRow :: Int -> Table -> Row
tableRow idx t = VU.slice base end t.content
  where
    base = t.row_width * idx
    end = t.row_width

data EGraph = EGraph {
    hash_lookup :: !(SymbolMap (HM.HashMap Row Id)),
    row_width :: !(SymbolMap Int),
    classes :: !(ClassMap AClass),
    union_find :: !UF
} deriving (Eq, Ord, Show, Generic)

mergeClass :: AClass -> SymbolMap Table -> (ClassSet, AClass)
mergeClass a b = (newReferences, AClass {
    class_id = a.class_id,
    tables = M.unionWith mergeTable (tables a) b,
    referenced_by = a.referenced_by,
    references = a.references `IS.union` bReferences
})
  where
    bReferences = foldMap (.references) b
    newReferences = bReferences IS.\\ a.references
data UpdatedEGraph = UpdatedEGraph {
    egraph :: !EGraph,
    new_data :: !(ClassMap (SymbolMap Table))
} deriving (Eq, Ord, Show, Generic)
applyUpdate :: UpdatedEGraph -> EGraph
applyUpdate ue = ue.egraph { classes =  L.foldl' addBackRef newClasses (M.toList newBackRefs) }
  where
    addBackRef :: ClassMap AClass -> (Id, ClassSet) -> ClassMap AClass
    addBackRef  classes (k,v) = classes & ix k . #referenced_by %~ IS.union v
    newBackRefs :: ClassMap ClassSet
    (newClasses, newBackRefs) = flip runState mempty $ MM.mergeA MM.preserveMissing (MM.mapMissing mkClass) (MM.zipWithAMatched combClass) (ue.egraph.classes) ue.new_data
    mkClass k symTables = AClass { class_id = k, tables = symTables, referenced_by = IS.empty, references = references }
      where references = foldMap (.references) symTables
    combClass k cls symTables = do
        let (newUses,out) = mergeClass cls symTables
        forM_ (IS.toList newUses) $ \s -> modify (M.insertWith IS.union s $ IS.singleton k)
        pure out
    


mergeTable :: Table -> Table -> Table
mergeTable a b = Table {
    row_width = a.row_width,
    content = mergeNaive a.row_width a.content b.content,
    references = IS.union a.references b.references
}
  where
    

mergeNaive :: Int -> VU.Vector Int -> VU.Vector Int -> VU.Vector Int
mergeNaive row_width l r = VU.concat $ map head $ L.group $ L.sort $ merge (toListOf (chunksOf row_width) l) (toListOf (chunksOf row_width) r)
  where
    merge [] [] = []
    merge [] r = r
    merge l [] = l
    merge lls@(l:ls) rrs@(r:rs) = case compare l r of
      EQ -> l : merge ls rs
      LT -> l : merge ls rrs
      GT -> r : merge lls rs
instance Hashable (VU.Vector Int) where
    hashWithSalt salt v = hashWithSalt salt (VU.toList v)

normalize :: (MonadState EGraph  m) => Id -> m Id
normalize i = do
    uf <- use #union_find
    let (o, uf') = UF.find uf i
    #union_find .= uf'
    pure o
normalizeRow  :: (MonadState EGraph  m) => Row -> m Row
normalizeRow = traverseOf each normalize

    
resolveE :: (MonadState EGraph m) => Symbol -> Row -> m (Maybe Id)
resolveE s r = do
    r' <- traverseOf each normalize r
    preuse (#hash_lookup . ix s . ix r')

-- | We have a prefix of the row, pretend it is filled with 0's
-- How do we compare?
comparePrefix :: RowPrefix -> Row -> Ordering
comparePrefix prefix row = go 0
  where
    go !i
      | i >= VU.length prefix = EQ -- FIXME is this broken?
      | otherwise = case compare (prefix VU.! i) (row VU.! i) of
         LT -> LT
         GT -> GT
         EQ -> go (i+1)
data OnMatch = GoLeft | GoRight
binarySearch :: OnMatch -> (Int -> Ordering) -> Int -> Int -> Maybe Int
binarySearch def step = go Nothing
  where
    go acc low high
      | high < low = acc
      | otherwise = case step mid of
         LT -> go acc low (mid-1)
         EQ -> case def of
            GoLeft -> go (Just mid) low (mid-1)
            GoRight -> go (Just mid) (mid+1) high
         GT -> go acc (mid+1) high
      where mid = low + (high - low) `div` 2

tableRows :: Table -> [Row]
tableRows t = build $ \cons nil -> 
  let
    chunks = tableSize t
    go i
      | i >= chunks = nil
      | otherwise = tableRow i t `cons` go (i+1)
  in go 0
-- [Note] if this is a stepping stone for full indices this is fine
-- Otherwise, we might want to consider incremental longest common prefix arrays
regionBoundary :: OnMatch -> Int -> Table -> RowPrefix -> Maybe Int
regionBoundary def l t prefix = binarySearch def checkIdx l (tableSize t-1)
  where
    checkIdx idx = comparePrefix prefix (tableRow idx t)

testTable :: Table
testTable = Table {row_width = 3, content = rows, references=mempty} 
  where
    rows = VU.fromList
         [ 0,0,0
         , 0,1,2
         , 0,1,3
         , 1,2,0
         , 1,2,2
         , 3,0,0
         ]

type RowPrefix = Row
lookupRange :: Table -> RowPrefix -> [Row]
lookupRange table prefix = build $ \cons nil ->
      let
        go i
          | i > r = nil
          | otherwise = tableRow i table `cons` go (i+1)
      in go l
  where
    (l,r) = case regionBoundary GoLeft 0 table prefix  of
      Nothing -> (1,0)
      Just l -> case regionBoundary GoRight (l+1) table prefix of
        Nothing -> (l,l)
        Just r -> (l,r)


data Modification = Mods { insertions :: ClassMap (SymbolMap Table), unifications :: VU.Vector (Id,Id) }
-- for insertions:
-- - insert into hashmap
-- - on collision, queue unification
-- - extend class table
-- - mark class table as dirty
-- for unifications:
-- - decide which class to remove
-- - queue insertions into new class
-- - mark the referenced_by classes as dirtied by the rewritten class
-- for normalization:
-- - sort and dedup all dirty tables
-- - rebuild hashtable
--
-- By using prefix tries/indices we wouldn't need sorting, and could defer normalization until we have too much garbage accumulated?
type RowQueue s = GV.Grow VU.MVector s Int
type ClassDict s a = D.Dictionary s VU.MVector Id VB.MVector a
type SymbolDict s a = D.Dictionary s VU.MVector Symbol VB.MVector a
data RebuildState s = RS {
    dirtiedClasses :: ClassMap ClassSet,
    new_rows :: ClassDict s (SymbolDict s (RowQueue s)),
    dirty_ids :: ClassSet,
    pending_merges :: S.Set (Id,Id),
    rewritten :: ClassSet,
    egraph :: EGraph
  } deriving (Generic)
data FRebuildState = FRS {
    dirtiedClasses :: ClassMap ClassSet,
    new_rows ::ClassMap (SymbolMap (VB.Vector (VU.Vector Int))),
    dirty_ids :: ClassSet,
    rewritten :: ClassSet,
    egraph :: EGraph
  } deriving (Eq, Ord, Show, Generic)


newRowsToTables :: (Monad m) => SymbolMap Int -> ClassDict s (SymbolDict s (RowQueue s)) -> m (ClassMap (SymbolMap Table))
newRowsToTables row_sizes cm = classMap `seq` pure classMap
  where
    -- absolutely horrendous hack to avoid a memory leak
    -- without the unsafeDupablePerformIO the lists have to be forced into memory

    classMap = M.fromList $ do
        (k,vs) <-  unsafeDupablePerformIO $ unsafeSTToIO (D.toList cm)
        pure $ (k,) $ M.fromList $ do
            (k2,v) <- unsafeDupablePerformIO  $ unsafeSTToIO (D.toList vs)
            pure (k2, mkTable (row_sizes ! k2) $ unsafeDupablePerformIO $ unsafeSTToIO $ GV.unsafeFreeze v)


runRebuild :: EGraph -> (forall s. RebuildT (ST s) a) -> (UpdatedEGraph, a)
runRebuild eg m = runST $ do
  rs <- mkRebuildState eg
  (a,rs') <- runStateT (unRebuildT m) rs
  newRows <- newRowsToTables rs'.egraph.row_width rs'.new_rows
  pure (UpdatedEGraph rs'.egraph newRows, a)

mkTable :: Int -> VU.Vector Int -> Table
mkTable row_width content = Table {content = naiveNormalize content, references = theReferences, ..}
  where
    theReferences = IS.fromList $ VU.toList content
    naiveNormalize = VU.concat . map head . L.group . L.sort . toListOf (chunksOf row_width)


freezeRebuildState :: (s ~ PrimState m, PrimMonad m) => RebuildState s -> m (FRebuildState)
freezeRebuildState s@RS{..} = do
    new_rows <- freezeDicts new_rows s.egraph.row_width
    pure FRS{..}
freezeDicts :: (s ~ PrimState m, PrimMonad m) => ClassDict s (SymbolDict s (RowQueue s)) -> SymbolMap Int -> m (ClassMap (SymbolMap (VB.Vector (VU.Vector Int))))
freezeDicts s rw = do
    s <- D.toList s
    o <- forM s $ \(k,v) -> do
        v <- freezeSymDicts v rw
        pure (k,v)
    pure $ M.fromList o
freezeSymDicts :: (s ~ PrimState m, PrimMonad m) => (SymbolDict s (RowQueue s)) -> SymbolMap Int -> m (SymbolMap (VB.Vector (VU.Vector Int)))
freezeSymDicts v rw = do
    v <- D.toList v
    v <- forM v $ \(k2,GV.Grow mv) -> do
       let width  = rw ! k2
       v <- VU.freeze mv
       pure $ (k2, VB.fromList $ toListOf (chunksOf width) v)
    pure $ M.fromList v



newtype RebuildT m a = RebuildT { unRebuildT :: StateT (RebuildState (PrimState m)) m a }
  deriving (Functor, Applicative, Monad, MonadReader r, MonadWriter w)
instance MonadTrans RebuildT where
    lift = RebuildT . lift
deriving instance (Monad m, s ~ PrimState m) => MonadState (RebuildState s) (RebuildT m)
instance PrimMonad m => PrimMonad (RebuildT m) where
    type PrimState (RebuildT m) = PrimState m
    primitive = RebuildT . primitive
-- popInserts :: Monad m => Id -> RebuildT m (SymbolMap [Row])
-- popInserts id = #pending_insertions . at id . non mempty <.=  mempty

-- TODO: keeping insertions seperate can be useful for incremental evaluation?
-- applyInsertionsTo :: Monad m => Id ->  RebuildT m ()
-- applyInsertionsTo c = do
--     ins <- popInserts c
--     iforOf_ (each <. each) ins $ \symbol row ->
--       queueInsert c symbol row

queueUnion :: MonadState (RebuildState s) m => Id -> Id -> m ()
queueUnion ar br =do
    a0 <- useEgg (normalize ar)
    b0 <- useEgg (normalize br)
    if (a0 == b0) 
    then traceM ("skip union " <> show (ar,br) <> "(=" <> show (a0,b0) <> ")")
    else do
        traceM ("queue union " <> show (ar,br) <> "(=" <> show (a0,b0) <> ")")
        let 
          (a,b)
            | a0 <= b0 = (a0,b0)
            | otherwise = (b0,a0)
        (#egraph . #union_find)%=(merge a b)
        #pending_merges . at (a,b) ?= ()


mkUnion :: forall m. (MonadState (RebuildState (PrimState m)) m, PrimMonad m, MonadInsert m) => Id -> Id -> m ()
mkUnion a0 b = do
  a <- useEgg (normalize a0)
  ioverM_ (#egraph . #classes . ix b . #tables . itraversed) $ \sym tab -> do
     forMOf_ (chunksOf tab.row_width) tab.content $ \row -> do
         reinsertAndQueue @m a sym row
  invalidated <- use (#egraph . #classes . singular (ix b) . #referenced_by)
  #egraph . #classes . at b .= Nothing
  #dirty_ids %= IS.union invalidated
  mold <- swapP (#new_rows . atM b) (pure Nothing)
  case mold of
      Nothing -> traceM ("skip normalizing new " <> show b)
      Just old -> do
         rw <- use (#egraph . #row_width)
         d <- freezeSymDicts old rw
         traceM ("old rows " <> show d)
         forIxP old (ieachP @m) $ \sym vecs -> do
             w <- getWidth sym
             if w == 0
             then reinsertAndQueue a sym VU.empty
             else do
                 forP vecs (GV.chunksOfM w) $ \row -> do
                     reinsertAndQueue a sym =<< VU.unsafeFreeze row
appUnions :: (MonadState (RebuildState (PrimState m)) m, PrimMonad m, MonadInsert m) => m ()
appUnions = do
    s <- swapP #pending_merges (pure S.empty)
    forM_ (S.toList s) $ \(a,b) -> do 
        traceM ("appUnions: " <> show (a,b))
        #pending_merges . at (a,b) .= Nothing
        mkUnion a b
    when (not $ S.null s) $ appUnions

reinsertAndQueue :: (PrimMonad m, MonadInsert m, MonadState (RebuildState (PrimState m)) m) => Id -> Symbol -> Row -> m ()
reinsertAndQueue c symbol row = (reinsert c symbol row) *> (mkInsert c symbol row)

useEgg :: (MonadState (RebuildState s) m) => State EGraph a -> m a
useEgg m = do
    e <- use #egraph
    let (o,e') = runState m e
    #egraph .= e'
    pure o
reinsert :: (
    MonadState (RebuildState (PrimState m)) m,
    PrimMonad m, MonadInsert m
  ) => Id -> Symbol -> Row -> m ()
reinsert c symbol row = do
  traceM ("reinsert: " <> show c <> " = " <> show symbol <> "(" <> show row <> ")")
  useEgg (resolveE symbol row) >>= \case
    Just o -> do
      queueUnion c o
    Nothing -> do
      #egraph . #hash_lookup . at symbol . non mempty . at row ?= c

-- getQueueVec :: PrimMonad m => Id -> Symbol -> RebuildT m (VM.MVector (PrimState m) Int)
newRowsFor :: (HasMonad m f, Functor f, s ~ (PrimState m), PrimMonad m) => Id -> Symbol -> MLensLike' f (RebuildState s) (RowQueue s)
newRowsFor cid symbol = #new_rows . atM cid . nonP (D.initialize 2) . atM symbol . nonP (GV.new 4)

type GrowVec s = GV.Grow VU.MVector s Int
class Monad m => MonadInsert m where
    mkInsert :: Id -> Symbol -> Row -> m ()
    default mkInsert :: (m ~ t n, MonadTrans t, MonadInsert n) => Id -> Symbol -> Row -> m ()
    mkInsert a b c = lift (mkInsert a b c)
instance (s ~ (PrimState m), PrimMonad m) => MonadInsert(RebuildT m) where
    mkInsert cid symbol row = RebuildT $ (newRowsFor cid symbol)&.GV.appendSlice (row)
instance (Monoid r, MonadInsert m) => MonadInsert (WriterT r m)
instance (MonadInsert m) => MonadInsert (IdentityT m)

traverseIntSet :: (Applicative f) => (Int ->  f Int) -> IS.IntSet -> f IS.IntSet
traverseIntSet f s = IS.foldr (\i s' -> IS.insert <$> f i <*> s') (pure IS.empty) s

-- | Go through all classes, queue inserts for any table affected by unificatio
reinsertOld :: PrimMonad m => ClassSet -> RebuildT m ()
reinsertOld dirty = do
    ioverM_ (#egraph . #classes . itraversed <.> #tables . itraversed) $ \(cid, symbol) table -> do
        unless (table.references `IS.disjoint` dirty) $ do
            forM_ (tableRows table) $ \row -> do
                row' <- useEgg (normalizeRow row)
                when (row' /= row) (reinsertAndQueue cid symbol row')
            refs' <- useEgg $ traverseIntSet normalize table.references
            #egraph . #classes . ix cid . #tables . ix symbol . #references .= refs'

newRows :: Lens' (RebuildState s) (ClassDict s (SymbolDict s (RowQueue s)))
newRows = #new_rows

getWidth :: (MonadState s1 m, HasField "egraph" s1 s1 s2 t, HasField "row_width" s2 t a a, Ixed a) => Index a -> m (IxValue a)
getWidth sym = use (#egraph . #row_width . singular (ix sym))

rewriteNewRows :: forall m. (PrimMonad m) => RebuildT m ()
rewriteNewRows = do
    usingIxP (newRows .$ ieachP <.>$ ieachP) $ \(cls, sym) xs -> do
        -- traceM ("rewriteNewRows: " <> show (cls, sym))
        rowWidth <- getWidth sym
        forP xs (GV.chunksOfM rowWidth) $ \chunk -> do
            -- normalize each chunk
            o <- execWriterT $ forP chunk eachP $ \entry -> do
                entry' <- useEgg (normalize entry)
                when (entry /= entry') $ tell (Any True)
                pure entry'
            -- and if the chunk changed, re-insert into the hashmap
            when (getAny o) $ do
                fchunk <- VU.freeze chunk
                reinsert cls sym fchunk
                -- if this causes a collision we need to redo this whole song and dance, so do tell!

toFixpoint :: (PrimMonad m)=> RebuildT m ()
toFixpoint = app_merges False
  where
      app_merges b = do
           has_pending <- use (#pending_merges . to S.size . to (>0)) 
           if not has_pending
           then when b rewrite_rows
           else do
               appUnions

               dirty <- use #dirty_ids
               #dirty_ids .= IS.empty
               reinsertOld dirty

               app_merges True

      rewrite_rows = do
         traceM "Rewrite new rows"
         rewriteNewRows
         app_merges False

mkEGraph :: SymbolMap Int -> EGraph 
mkEGraph width = EGraph mempty width mempty UF.empty
mkRebuildState :: PrimMonad m => EGraph -> m (RebuildState (PrimState m))
mkRebuildState eg = do
   dict <- D.initialize  32
   pure $ RS mempty dict mempty mempty mempty eg

newClass :: Monad m => RebuildT m Id
newClass = do
  o <- use (#egraph . #classes . to M.size)
  #egraph . #classes . at o ?= AClass o mempty mempty mempty
  pure o

mkApp :: PrimMonad m => Symbol -> [Id] -> RebuildT m Id
mkApp sym args = do
    m <- useEgg (resolveE sym vargs)
    case m of
      Just o -> pure o
      Nothing -> do
        cid <- newClass
        reinsertAndQueue cid sym vargs
        pure cid
  where vargs = (VU.fromList args)

testInsert :: (PrimMonad m) => RebuildT m ()
testInsert = do
  c1 <- newClass
  reinsertAndQueue c1 2 (VU.fromList [])
  c2 <- newClass
  c3 <- newClass
  reinsertAndQueue c3 3 (VU.fromList [c1])
  c4 <- newClass
  reinsertAndQueue c4 3 (VU.fromList [c2])
  reinsertAndQueue c2 2 (VU.fromList [])
  toFixpoint

doTest :: UpdatedEGraph
doTest = fst $ runRebuild (mkEGraph $ M.fromList [(2,0), (3,1)]) testInsert


(!) :: HasCallStack => ClassMap k -> Int -> k
(!) m k = case m M.!? k of
  Nothing -> error ("No such key: " <> show k)
  Just x -> x
