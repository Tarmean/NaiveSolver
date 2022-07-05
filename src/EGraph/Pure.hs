{-# Language DeriveGeneric #-}
{-# Language TupleSections #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
module EGraph.Pure where
import qualified Data.Map as M
import Data.Generics.Labels ()
import Control.Lens
import Control.Monad.State
import EGraph.Types
import GHC.Generics (Generic)
import qualified Data.Set as S
import Data.Foldable (asum)
import Data.List (group, sort)
import qualified Data.Vector.Unboxed as VU
import Optics.Utils

-- Naive and inefficient egraph implementaion

matchesOf :: Id -> Symbol -> VU.Vector Id -> (VU.Vector Id -> M ()) -> M ()
matchesOf = undefined

data UF = UF (M.Map Id Id) Int
  deriving (Eq, Ord, Show, Generic)

genId :: UF -> (UF, Id)
genId (UF m i) = (UF m (i+1), Id i)

find :: UF -> Id -> (UF, Id)
find (UF m0 x) = go m0
  where
    go m i = case m M.!? i of
      Nothing -> (UF m x, i)
      Just o -> go (M.insert i o m) o
merge :: Id -> Id -> UF -> UF
merge r l m = UF (M.insert l' r m') x
  where
    (UF m' x, l') = find m l


-- FIXME: split class into directory of symbols
-- TODO: update parentIds? after update?
data Class = Class { classId :: Id, elems :: [Elem], parents :: S.Set (Id, Elem) }
  deriving (Eq, Ord, Show, Generic)
-- This acts as a normalized database (or bipartite graph if that's more your thing)
-- Classes stand for sets of equal types
-- - they have a unique ID as an identity
-- - we can merge classes
-- - we can get a list of classes which contain an element with `$Symbol` as root (for querying)
-- - we can get a list of elements in the class (for followup after we have the classes, the list is sorted)
--
--Elements have the form `mySymbolName($class1,$class2,$class3)`, i.e. a symbol head and n classes as arguments
-- Problem with the merging:
data EGraph = EGraph {
    classes :: M.Map Id Class,
    lookup :: M.Map Elem Id,
    equivIds :: UF,
    index :: M.Map Symbol [Id]
} deriving (Eq, Ord, Show, Generic)

emptyPending :: Pending
emptyPending = Pending [] []
emptyUF :: UF
emptyUF = UF mempty 0
emptyEGraph :: EGraph
emptyEGraph = EGraph mempty mempty emptyUF mempty

runEgg :: M () -> EGraph
runEgg m = fst $ execState m (emptyEGraph, emptyPending)

data Pending = Pending { pendingUnification :: [(Id, Id)], pendingInserts :: [(Elem, Id)] }
  deriving (Eq, Ord, Show, Generic)

test :: State (EGraph, Pending) ()
test = do
  _ <- insertRExp (RExp (Elem (Symbol 0) [RExp (Elem (Symbol 1) []), RExp (Elem (Symbol 1) [])]))
  _ <- insertRExp (RExp (Elem (Symbol 0) [RExp (Elem (Symbol 2) []), RExp (Elem (Symbol 1) [])]))
  _ <- insertRExp (RExp (Elem (Symbol 5) [RExp (Elem (Symbol 2) []), RExp (Elem (Symbol 3) [RExp (Elem (Symbol 2) [])])]))
  _ <- insertRExp (RExp (Elem (Symbol 6) [RExp (Elem (Symbol 7) [RExp (Elem (Symbol 10) [])]), RExp (Elem (Symbol 8) [RExp (Elem (Symbol 7) [RExp (Elem (Symbol 10) [])])])]))
  pure ()

insertRExp :: RExp -> M Id
insertRExp (RExp (Elem s exp)) = do
  exp' <- traverse insertRExp exp
  elemClass (Elem s exp')


naiveSearch :: Pat -> M [(Id, M.Map Var Id)]
naiveSearch (Pat e@(Elem s0 _)) = do
    idx <- use (egg . #classes)
    ls0 <- use (egg . #index . at s0 . non mempty)
    let
        resolveCls a = idx M.! a
        go (Elem s args) x m = do
          let cls = resolveCls x
          let els = filter (\a -> fSymbol a == s) $ elems cls
          asum $ map (check m . zip args . argIds) els
        check m [] = pure m
        check m ((Right (Pat p), c):xs) = do
           m1 <- go p c m
           check m1 xs
        check m ((Left v, c):xs) = case M.lookup v m of
           Nothing -> check (M.insert v c m) xs
           Just c' | c == c' -> check m xs
           _ -> mempty
    pure $ asum $ map (\x -> (x,) <$> go e x mempty) ls0


type Pos = Int
data TraceEntry = Child { childOf :: Pos, childIdx :: Int, childTyp :: Either Var Symbol }
data MatchTrace = MT Symbol [TraceEntry]

elemClass :: Elem -> M Id
elemClass e = do
    e <- normalize e
    use (egg . #lookup . at e) >>= \case
      Just o -> pure o
      Nothing -> do
        classId <- mkId
        let cls = Class classId [e] mempty
        forM_ (argIds e) $ \p -> do
          egg . #classes . ix p . #parents %= S.insert (classId, e)
        egg . #classes . at classId ?= cls
        egg . #lookup . at e ?= classId
        egg . #index . at (fSymbol e) . non mempty %= (classId:)
        pure classId

type M a = State (EGraph, Pending)  a

egg :: Lens (EGraph, Pending) (EGraph, Pending) EGraph EGraph
egg = _1

mkId :: M Id
mkId = do
  uf <- use (egg . #equivIds)
  let (uf', i) = genId uf
  egg . #equivIds .= uf'
  pure i
mergeId :: Id -> Id -> M ()
mergeId l r = do
  uf <- use (egg . #equivIds)
  let uf' = merge l r uf
  egg . #equivIds .= uf'
resolveId :: Id -> M Id
resolveId l = do
  uf <- use (egg . #equivIds)
  let (uf', i) = find uf l
  egg . #equivIds .= uf'
  pure i

-- classIx :: Id -> Lens' EGraph Class
-- classIx i = #classes . singular (ix i)

processMerges :: [(Id, Id)] -> M ()
processMerges ls =do
  o <- traverse (uncurry merge1) ls
  processAllPending $ S.toList $ mconcat o
  normalizeClassElems
  recalculateIndex

processAllPending :: [(Id, Elem)] -> M ()
processAllPending = go
  where
      go [] = pure ()
      go ls = do
        ls' <- traverse (uncurry reinsertNode) ls
        go (S.toList $ mconcat ls')
reinsertNode :: Id -> Elem -> M (S.Set (Id, Elem))
reinsertNode cls oldElem = do
    elem <- normalize oldElem
    newCls <- elemClass elem
    merge1 newCls cls

uniqSorted :: Ord a => [a] -> [a]
uniqSorted = fmap head . group

normalize :: Elem -> M Elem
normalize e@Elem { argIds } = do
   argIds' <- traverse resolveId argIds
   pure e{argIds=argIds'}

normalizeClassElems :: M ()
normalizeClassElems =
  overM (egg . #classes . traversed . #elems) $ \elems ->  do
    elems' <- traverse normalize elems
    pure $ uniqSorted $ sort elems'

recalculateIndex :: M ()
recalculateIndex = do
  egg . #index .= mempty
  classes <- use (egg . #classes)
  iforOf_ (itraversed <. (#elems . to (fmap fSymbol) . to uniqSorted . each)) classes $ \cls h -> do
       egg . #index . at h . non mempty %= (cls:)

merge1 :: Id -> Id -> M (S.Set (Id, Elem))
merge1 l r = do
  l <- resolveId l
  r <- resolveId r
  if l == r
  then pure mempty
  else do
    cl <- gets (^?! egg . #classes . ix l)
    cr <- gets (^?! egg . #classes . ix r)
    egg . #classes . at r .= Nothing
    egg . #classes . at l ?= Class l (elems cl <> elems cr) (parents cl <> parents cr)
    mergeId l r
    let newPending = parents cr
    pure newPending

