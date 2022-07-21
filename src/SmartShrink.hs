{-# LANGUAGE RecordPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QualifiedDo #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE DefaultSignatures #-}
module SmartShrink where

import Twee.Pretty

-- import Data.Express
-- import Data.Express.Utils.Typeable (tyArity)
import Control.Monad.State 
import Control.Monad.Cont
import Control.Applicative (Alternative (..), Applicative (..))
import Data.Data hiding (TyCon)
import Data.Kind (Type)
import GHC.Stack (HasCallStack)
import Control.Monad.Writer (MonadWriter(tell), WriterT (runWriterT), Endo (..), execWriterT)
import qualified Data.Map.Strict as M
import Data.Dynamic
import GHC.Generics

import Data.Typeable
import qualified Type.Reflection as TR
import Type.Reflection (SomeTypeRep)
import Control.Monad.Identity
import GHC.TypeLits (type (+), Nat, type (-), KnownNat, natVal, natVal')
import qualified IndexedWalk as Ix
import GHC.IO (unsafePerformIO)
import Data.IORef
import qualified Twee.Base as TB
import qualified Twee.Term as T
import qualified Data.Label as T
-- import Data.Express.Utils (sortOn)
-- import Test.Extrapolate
-- import Test.Extrapolate.Core (grounds)
-- import qualified Test.Speculate.Expr as SE
-- import Test.Speculate.Engine (theoryAndRepresentativesFromAtoms)
-- import GHC.Base (TyCon(..))
import qualified Data.List as L
import QuickSpec.Internal.Term
import qualified QuickSpec.Internal.Type as QT
import QuickSpec.Internal.Haskell (con, Constant)
import qualified QuickSpec.Internal.Haskell as QH
import QuickSpec.Internal.Type (Typed(..))
import Monad.Zipper
import Monad.StateT2
import Data.Maybe (fromMaybe)
import qualified Data.Set as S
import Debug.Trace
import Data.Foldable (asum)


showTypRep :: TypeRep  -> String
showTypRep (TR.SomeTypeRep r) = showTypRep' r

showTypRep' :: TR.TypeRep a  -> String
showTypRep' rep = case rep of
  TR.Fun f a -> showTypRep' f <> " -> " <> showTypRep' a
  TR.App f a -> "App { l = " <> showTypRep' f <> ", r =" <> showTypRep' a <> " }"
  TR.Con c -> "Cons { cons = " <> show c <> " }"

-- showTyCon :: TyCon -> String
-- showTyCon s = case s of
--     TyCon a b c d _ f -> "TyCon " <> show (c,d,f)
data Pos = AStruct TypeRep String | PartialApp String TypeRep Int
  deriving Show
data ArgKind = Recursive | Arg TypeRep
  deriving Show
type FunTyp = ([TypeRep], TypeRep)

getArgs :: TypeRep -> FunTyp
getArgs (TR.SomeTypeRep tyRep) = go tyRep []
  where
    go :: TR.TypeRep a -> [TypeRep] -> FunTyp
    go (TR.Fun a r) acc = go r (TR.SomeTypeRep a : acc)
    go r acc = (reverse acc, TR.SomeTypeRep r)
recArgs :: FunTyp -> [Int]
recArgs (args, r) = [i | (arg, i) <- zip args [0..], arg == r]
nonRecArgs :: FunTyp -> [(Int, TypeRep)]
nonRecArgs (args, r) = [(i,arg) | (arg, i) <- zip args [0..], arg /= r]


data Bin f a = App f (Bin f a) (Bin f a) | Leaf f a | IVar f Var
    deriving (Show, Eq, Ord, Typeable, Generic)
instance Typed a => Typed (Bin () a) where
  typ (Leaf _ a) = typ a
  typ (IVar _ v) = typ v
  typ (App _ f x) = typ f `QT.applyType` typ x

  typeSubst_ s t = case t of
    Leaf f a -> Leaf f (typeSubst_ s a)
    IVar f v -> IVar f (typeSubst_ s v)
    App f x y -> App f (typeSubst_ s x) (typeSubst_ s y)

instance (Pretty f, Pretty a) => Pretty (Bin f a) where
  pPrint (App _ l r) = pPrint l <> "(" <> pPrint r <> ")"
  pPrint (Leaf _ a) = pPrint a
  pPrint (IVar _ v) = pPrint v
data instance Dir (Bin f a) = BinFun | BinArg
    deriving (Show, Eq, Ord, Typeable, Generic, Bounded, Enum)
instance Walkable (Bin f a) where
   data instance ZipperStep (Bin f a) = AppFun f (Bin f a) | AppArg f (Bin f a)
     deriving (Eq, Ord, Show)
   zGo BinFun = unCons $ \case
     (App k f a) -> Just (AppArg k a, f)
     _ -> Nothing
   zGo BinArg = unCons $ \case
     (App k f a) -> Just (AppFun k f, a)
     _ -> Nothing
   zApp (AppFun k f) x = App k f x
   zApp (AppArg k a) x = App k x a


data instance Dir [a] = DCons
    deriving (Show, Eq, Ord, Typeable, Generic, Bounded, Enum)
instance Walkable [a] where
    data instance ZipperStep [a] = ZCons a
    zGo DCons = unCons $ \case
      [] -> Nothing
      (x:xs) -> Just (ZCons x,xs)
    zApp (ZCons x) xs = x:xs


newtype ShrinkT x o (r::Type) m a = ShrinkT { unShrink :: ZipperT x o (ContT r m) a }
  deriving (Functor, Applicative, Monad, MonadZipper o)
-- deriving instance Monad m => MonadState (ShrinkState f o) (ShrinkT' f o r m)

shrinkT :: ((o -> ContT r m x, Zipper o) -> ((a, (o -> ContT r m x, Zipper o)) -> m r) -> m r) -> ShrinkT x o r m a
shrinkT f = ShrinkT $ ZipperT $ StateT $ \s -> ContT $ \k -> f s k
runShrinkT :: r1 -> ShrinkT r1 r1 r2 m a -> ((a, Zipper r1) -> m r2) -> m r2
runShrinkT o m k = runContT (runZipperT pure o (unShrink m)) k

data OraclingT m a = O (m (a, (Bool -> OraclingT m a)))
newtype RoseForestT m a = RoseF { unForestT :: m (RoseCell m a)}
  deriving (Functor)
deriving instance (Show (m (RoseCell m a)), Show a) => Show (RoseForestT m a)
data RoseCell m a = RoseNil | RoseCell a (RoseForestT m a) (RoseForestT m a)
  deriving (Functor)

printRose :: Show a => RoseForestT Identity a  -> IO ()
printRose r0 = putStrLn $ unlines $ go 0 r0 []
  where
    go i (RoseF (Identity rose)) = case rose of
        RoseNil -> id
        RoseCell c m r -> ((pad i <> "|" <> show c) :) . go (i+2) m . go i r
    pad i = replicate i ' '
deriving instance (Show (RoseForestT m a), Show a) => Show (RoseCell m a)
instance Applicative m => Applicative (RoseForestT m) where
  pure = RoseF . pure . pure
  f <*> a = RoseF $ liftA2 (<*>) (unForestT f) (unForestT a)
instance Applicative m => Applicative (RoseCell m) where
  pure a = RoseCell a (RoseF $ pure RoseNil) (RoseF $ pure RoseNil)
  RoseNil <*> _ = RoseNil
  _ <*> RoseNil = RoseNil
  RoseCell f fl fr <*> RoseCell a al ar = RoseCell (f a) (fl <*> al) (fr <*> ar)
instance Applicative m => Semigroup (RoseForestT m a) where
   l <> r = l <|> r
instance Applicative m => Monoid (RoseForestT m a) where
   mempty = empty
instance Applicative m => Alternative (RoseForestT m) where
  empty = RoseF $ pure empty
  l <|> r = RoseF $ liftA2 (<|>) (unForestT l) (unForestT r)

instance Applicative m => Alternative (RoseCell m) where
  empty = RoseNil
  RoseNil <|> a = a
  (RoseCell a l m) <|> r = RoseCell a l (RoseF $ fmap (<|> r) $ unForestT m )
  
class Monad m => MonadVar m where
    mkVar :: QT.Type -> m Var
    default mkVar :: (m ~ t n, MonadTrans t, MonadVar n) => QT.Type -> m Var
    mkVar = lift . mkVar
runVarT :: Monad m => VarT m a -> m a
runVarT (VarT m) = evalStateT m 0

instance MonadVar m => MonadVar (ZipperT r o m)
instance MonadVar m => MonadVar (StateT o m)
newtype VarT m a = VarT { unVarT :: StateT Int m a }
  deriving (Functor, Applicative, Monad, MonadWriter s, MonadZipper o, MonadTrans, Alternative, MonadOut r, MonadOracle)
instance MonadState s m => MonadState s (VarT m) where
  get = VarT (lift get)
  put = VarT . lift . put
instance Monad m => MonadVar (VarT m) where
    mkVar t = VarT $ do
      i <- get
      put (i+1)
      pure (V t i)
instance (Monoid o, MonadVar m) => MonadVar (WriterT o m)
-- class MonadZipper o m => MonadExtract m o | m -> o where
    
class Monad m => MonadOracle m where
    checkpoint :: m ()
    default checkpoint :: (m ~ t n, MonadTrans t, MonadOracle n) => m ()
    checkpoint = lift checkpoint
instance MonadOracle m => MonadOracle (StateT s m)
instance (Monoid s, MonadOracle m) => MonadOracle (WriterT s m)

-- (doRewrite >> checkPoint ) `orElse` doNothing

-- i <- oneOf [1,2,3]
-- doRewrite i
-- checkpoint

joinForest :: Monad m => m (RoseForestT m a) -> RoseForestT m a
joinForest = RoseF . join . fmap unForestT
instance (Walkable o, Monad m) => MonadOracle (ShrinkT x o (RoseForestT m x) m) where
    checkpoint = do
        o <- getOut
        shrinkT $ \s k -> do
             pure $ RoseF $ pure (RoseCell o (joinForest $ k ((), s)) empty)

instance (Monad m, Walkable o) => MonadOut x (ShrinkT x o r m) where
    getOut = ShrinkT getOut

runShrinkForest :: (Walkable x, Monad m) => x -> ShrinkT x x (RoseForestT m x) m a -> RoseForestT m x
runShrinkForest o m = joinForest $ runShrinkT o m (\(_,a) -> pure empty)
  -- where
  --   foo :: Applicative m => x -> m (RoseForestT m x)
  --   foo x = pure (pure x)

-- runShrinkList :: o -> ShrinkT o o a [] a -> [a]
-- runShrinkList e (ShrinkT m) = runContT (evalZipperT pure e m) pure

class Applicative m => Propagate m o | o -> m where
    mkApp:: o -> o -> m o
    fromLeaf :: Constant -> m o
    fromVar :: Var -> m o
-- infixl 9 @:
-- (@:) :: Bin o a -> Bin o a -> m (Bin o a)
newtype UniqTag = UT { getUniq :: Int }
popNext :: StateT Int Identity Int
popNext = do
   s <- get
   put (s+1) 
   pure s
instance Propagate (State Int) Int where
    mkApp _ _ = popNext
    fromLeaf _ = popNext
    fromVar _ = popNext
(@:) :: Bin () a -> Bin () a -> Bin () a
(@:) l r = App () l r
leaf :: Propagate m o => Constant -> m (Bin o Constant)
leaf c = flip Leaf c <$> fromLeaf c
-- varLeaf :: Propagate m o => Var -> m (Bin o Constant)
-- varLeaf c = Leaf <$> fromLeaf c

-- l @: r = App () l r
class MkExpr a where
   expr :: a -> (Bin () Constant)
instance (Typeable a, Typeable b, MkExpr a, MkExpr b) => MkExpr (a,b)  where
   expr a = Leaf () (con "(,)" ((,) :: a -> b -> (a,b))) @: expr (fst a) @: expr (snd a)
instance (Typeable a, Typeable b, Typeable c, MkExpr a, MkExpr b, MkExpr c) => MkExpr (a,b,c)  where
   expr (a,b,c) = Leaf () (con "(,,)" ((,,) :: a -> b -> c -> (a,b,c))) @: expr a @: expr b @: expr c
instance (Typeable a, MkExpr a) => MkExpr [a]  where
   expr a = go a
     where
       go (x:xs) = Leaf () (con ":" ((:) @a)) @: expr x @: go xs
       go [] = Leaf () (con "[]" ([] :: [a]))
instance MkExpr Char  where
    expr c = Leaf () (con (show c) c)
instance MkExpr Int  where
    expr c = Leaf () (con (show c) c)

-- runNumbering :: State Int a -> a
-- runNumbering = evalState 
-- test :: RoseForestT Identity Expr
-- test = runShrinkForest (expr ('a', "bcd")) $ do
--     assertCtor @((Char, String)) $ do
--        intoField @1 $ do
--            isField @String
--            replace ""
--            checkpoint
           -- assertCtor @(Char ': String) $ do
             -- pure ()
           -- intoField @0 $ do
-- test2 :: [Expr]

test2 :: RoseForestT Identity (Bin () Constant)
test2 = runShrinkForest (expr (1::Int,[2::Int,1,3], "xxy"::String)) $ runVarT $ do
    varUniqs (eachLeaf . onlyIf notFunction)

pick :: Alternative f => [a] -> f a
pick = asum . map pure
tryModify :: (MonadZipper (Bin () Constant) m, Typeable a, MkExpr a) => (a -> a) -> m ()
tryModify f = do
    s <- cursor
    case s of
      Leaf _ c -> case QT.fromValue (QH.con_value c) of
        Just (Identity (o :: a)) -> do
          let l' = expr (f o)
          setCursor $ l'
        _ -> pure ()
      _ -> pure ()
          
    -- varUniqs (eachLeaf . onlyIf notFunction)
    -- try (groupExprs @Char >> checkpoint)

try :: Alternative f => f () -> f ()
try m = m <|> pure ()

tryEager :: Alternative f => f () -> f ()
tryEager m = m <|> pure ()

pop :: MonadState [a] m => m (Maybe a)
pop = do
    s <- get
    case s of
        [] -> pure Nothing
        (x:xs) -> put xs >> pure (Just x)

type Visitor o = (forall n. MonadZipper o n => n () -> n ())
-- viewing :: (MonadZipper o n) => Visitor o -> ZipperT r [o] n () -> n ()
-- viewing vis x = do
--    undefined
   -- o <- execWriterT $ vis (cursor >>= tell . Endo . (:))
   -- o' <- extractZipperT rez (appEndo o []) x
   -- evalStateT (vis (pop >>= maybe (pure ()) setCursor)) o'

   

isVar :: Bin k o -> Bool
isVar (IVar _ _) = True
isVar _ = False

class (MonadZipper x m, MonadZipper y n) => HasView m n x y | m y -> n, n x -> m where
    zoomShrink :: m y -> (y -> m ()) -> n a -> m a
instance (Walkable y, Walkable x, Monad m) => HasView (ZipperT r x m) (ZipperT r y m) x y where
    zoomShrink f t = walkIntoM f t
instance (Walkable x, Walkable y) => HasView (ShrinkT v x r m) (ShrinkT v y r m) x y where
  zoomShrink f t x = ShrinkT (zoomShrink (unShrink f) (unShrink . t) (unShrink x))
instance (HasView m n x y) => HasView (VarT m) (VarT n) x y where
    zoomShrink f t m = VarT $ StateT $ \s -> 
      let 
        unV :: VarT m a -> m a
        unV v = fmap fst $ runStateT (unVarT v) s
      in zoomShrink (unV f) (unV . t) (runStateT (unVarT m) s)
    
listView :: (HasView m n o [o]) => Visitor o -> n a -> m a
listView v = zoomShrink getter setter
  where
    getter = fmap (`appEndo` [])$ execWriterT $ v (cursor >>= tell . Endo . (:))
    setter = evalStateT (v (pop >>= maybe (pure ()) setCursor))
groupedView :: (HasView m n o [o], Ord k, Pretty o, Pretty k) => Visitor o -> (o -> k) -> (k -> n ()) -> m ()
groupedView v k m = do
   ls <- getter
   let ks = M.fromListWith (<>) [(k x, [x]) | x <- ls]
   traceM $ render (pPrint ks)
   forM_ (M.toList ks) $ \(theKey,theVals) -> do
       -- traceM $ render ("hewwo" <>pPrint (theKey, theVals))
       zoomShrink (pure theVals) (setter theKey) (m theKey)
  where
    getter = fmap (`appEndo` [])$ execWriterT $ v (cursor >>= tell . Endo . (:))
    setter p = evalStateT (v (onlyIf (\x -> k x == p) (pop >>= maybe (pure ()) setCursor)))

varUniqs :: (o ~ Bin () f, Typed o, MonadVar n, Ord o, HasView m n o [o], Pretty f, Alternative n, MonadOracle n) => Visitor o -> m ()
varUniqs p = groupedView p id $ \k -> do
    s <- cursor
    when (length s > 1) $ try $ do
        v <- mkVar (typ k)
        modCursor $ map (\_ -> IVar () v)
        checkpoint

notFunction :: Typed a => a -> Bool
notFunction v = case typ v of
    (T.App (T.F _ QT.Arrow) _) -> False
    _ -> True

modCursor :: MonadZipper o m => (o -> o) -> m ()
modCursor p = do
  s <- cursor
  setCursor (p s)
setListVal :: (MonadZipper [o] m) => o -> m ()
setListVal x = do
    ls <- cursor
    case ls of
      [] -> pure ()
      (_:xs) -> setCursor (x:xs)

rewriteConstants :: forall m n o. (Typed o, HasView m n o [o]) => QT.Type -> n () -> m ()
rewriteConstants ty = listView (leafsWithType ty)

shrinkList :: MonadZipper [o] m  => m ()
shrinkList = undefined

leafsWithType :: (MonadZipper p m, Typed p) => QT.Type -> m () -> m ()
leafsWithType theType m = eachLeaf (onlyIf typMatches m)
  where typMatches e = typ e == theType

typeRepOf :: forall a. Typeable a => QT.Type
typeRepOf = QT.typeRep ( undefined :: proxy a )


listHead :: MonadZipper [o] m => m (Maybe o)
listHead = cursor >>= \case
  (x:_) -> pure (Just x)
  [] -> pure Nothing
--    changeList es = flipped
--      where
--        m = M.fromListWith (++) (zip es $ map pure [(0::Int)..])
--        flipped :: [Bin f o]
--        flipped = map snd $ L.sortOn fst [(v,vr) | (k,vs) <- M.toList m, v <- vs, vr <- mkVar k <$> vs]
--        mkVar k vs
--          | length vs <= 1 = k
--          | otherwise =  mkVar (V (QT.typ k) (head vs))
         

dynamicOf :: SomeTypeRep -> Dynamic
dynamicOf (TR.SomeTypeRep tr)
  | Just HRefl <- checkKind tr = Dynamic tr undefined
  | otherwise = error ("Invalid typerep for var " <> show tr)

checkKind :: TR.TypeRep (a :: k) -> Maybe (k :~~: Type)
checkKind tr = TR.eqTypeRep (TR.typeRepKind tr) (TR.typeRep @Type)


--
--
--  
   


isApp :: Bin k o -> Bool
isApp (App _ _ _) = True
isApp _= False
leavesOf :: (MonadZipper o m, Bounded (Dir o), Enum (Dir o)) => (o -> Bool) -> m () -> m ()
leavesOf p m = eachLeaf (onlyIf p m)
whenType :: (Typed o, MonadZipper o m) => QT.Type -> m () -> m ()
whenType ty m = do
    s <- cursor
    if (typ s == ty)
    then m
    else pure ()

instance MonadTrans (ShrinkT x o r) where
    lift sm = ShrinkT $ lift $ lift sm

constContT :: m r -> ContT r m a
constContT m = ContT $ \_ -> m
instance (Applicative m, Monoid r) => Alternative (ShrinkT x o r m) where
    empty = ShrinkT $ lift $ constContT $ pure @m (mempty @r)
    ShrinkT x <|> ShrinkT y = ShrinkT $ ZipperT $ StateT $ \z -> ContT $ \c -> liftA2 (<>) (ml x z c) (ml y z c)
      where
        ml m z c = (runContT (runStateT (unZipperT m) z) c)
instance (Applicative m, Monoid r) => MonadPlus (ShrinkT x o r m) where
    mzero = empty
    mplus = (<|>)
instance (Applicative m, Monoid r) => MonadFail (ShrinkT x o r m) where
    fail _ = empty

consArg :: forall t m k o x. (o ~ Bin k x, Typeable t, MonadZipper o m, Alternative m, Typed o) => t -> Int -> m ()
consArg t i = do
   replicateM_ (argCount - i - 1) (step BinFun)
   block $ do
       -- briefly go the rest of the way to check the constructor is correct
       replicateM_ (i+1) (step BinFun)
       assertTy tyrep
   step BinArg
 where
   tyrep = QT.typeRep (undefined :: proxy t)
   argCount = QT.typeArity tyrep

assertTy :: (Typed o, MonadZipper o m, Alternative m) => QT.Type -> m ()
assertTy tyrep = do
    s <- cursor
    guard (typ s == tyrep)


block :: (MonadZipper o m) => m a -> m a
block m = do
  remember
  o <- m
  recall
  pure o

doIn :: (Alternative m, MonadZipper o m) => Dir o -> m a -> m a
doIn dir m =  step dir *> m <* up
-- inR :: (Alternative m, MonadZipper o m) => m a -> m a
-- inR m =  tryStep zright *> m <* tryStep zup
-- goR :: (Alternative m, MonadZipper o m) => m ()
-- goR = tryStep zright
-- goL :: (Alternative m, MonadZipper o m) => m ()
-- goL = tryStep zleft

tryIn :: (MonadZipper o m) => Dir o -> m a -> m (Maybe a)
tryIn dir m = do 
   stepBool dir >>= \case
     False -> pure Nothing
     True -> fmap Just m <* up



type family Arity a where
    Arity (x -> y) = 1 + Arity y
    Arity a = 0
type FieldOf_ :: forall {k1}. Nat -> k1 -> Type
type family FieldOf_ (n :: Nat) (a :: k) where
    FieldOf_ 0 (x a) = a
    FieldOf_ n ((e :: k1 -> k) (b :: k1)) = FieldOf (n - 1) e

type family ArgCount a where
    ArgCount (x a) = 1 + ArgCount a
    ArgCount x = 0
type family FieldOf n a where
  FieldOf n a = FieldOf_ (ArgCount a - n - 1) a

newtype IsField c m a = IsField { unField :: m a}
  deriving (Functor, Applicative, Monad, Alternative, MonadState s, MonadWriter r, MonadOracle)
instance MonadTrans (IsField c) where
    lift = IsField

isField :: forall c m. Applicative m =>IsField c m ()
isField = pure ()
getInt :: forall n. KnownNat n => Int
getInt = fromInteger (natVal @n undefined)
getTypeable :: forall c. Typeable c => TypeRep
getTypeable = typeRep (undefined :: proxy c)

{-# NOINLINE myCount #-}
myCount :: IORef Int
myCount = unsafePerformIO $ newIORef (0::Int)

{-# INLINE incCount #-}
incCount :: a -> a
incCount a = unsafePerformIO (modifyIORef' myCount (+1)) `seq` a
getCount :: IO Int
getCount = readIORef myCount

-- myTest :: [Int] -> Bool
-- myTest ls 
--   | snd $ incCount (ls, False) = undefined
--   | otherwise = length ls > i ==> (ls !! 0::Int) /= 1+(ls !! i)
--   where
--     i =1
-- intTh :: [[Expr]]
-- intTh = [[val @Int 0], [value "+" ((+) @Int), value "*" ((*) @Int), value "abs" (abs @Int),val @Int 1, val @Int (-1)], [val @Int 2]]
-- ev :: Expr -> Expr -> Bool
-- ev a b 
--   | Just l <- evaluate @Int a
--   , Just r <- evaluate @Int b
--   = l == r
--   | otherwise = False

-- testS = theoryAndRepresentativesFromAtoms ev 8 intTh
