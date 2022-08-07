{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
module SmartShrinkTest where
import Data.Data (Data, Typeable)
import GHC.Generics (Generic)
import Test.QuickCheck
import Generic.Random (genericArbitrary, uniform, withBaseCase, genericArbitraryRec, (%))
import Debug.Trace
import Control.Applicative
import Data.IORef
import GHC.IO (unsafePerformIO)
import Control.Spoon (teaspoon)
import Data.Maybe (isNothing, fromJust)
import qualified Data.Map as M
import Control.DeepSeq
import System.Timeout (timeout)
import Control.Monad
import Monad.Snapshot()

import qualified Data.List as L
import Data.Data.Lens
import Control.Lens
import SmartShrink (runShrinkForest, shrinkTree, RoseForestT, downwardM, HasIdx(..), MergeMap (unMergeMap), depsMap, isRelevant, flipChildren, navigator, runVarTFrom, MonadVar (mkVar, setVar), seqForest, traceForest)
import Monad.Zipper (recursive, RecView (down), cursors, MonadZipper (cursor), up, pull)
import qualified Generic.Random.Internal.Generic as G
import Test.StrictCheck.Shaped
import Generics.SOP (type (:.:) (Comp), Associativity (..), All, I (..))
import Control.Monad.State
import Generics.SOP.Constraint (Top)
import Data.Monoid (Endo(..))
import Data.Typeable as Typ
import Generics.SOP.NP
import qualified Generics.SOP as SOP
import Control.Monad.Writer (execWriterT)
import Control.Zipper (rightward)
import Monad.Critical (evalCritical, evalCriticalT, getCriticals, MonadCritical)
import ShrinkLoop (replaceNode, smartLoop, hoistNode, GenAction, hoistInCrit)
import Monad.Graph (MonadGraphMut (addDeps), runGraphT, getHidden)
import Monad.Oracle (MonadOracle, checkpoint)
import Monad.Snapshot
import Data.Coerce (coerce)
import Monad.Cut
import qualified Data.Set as S
import Data.Utils
import qualified Data.Foldable as F

data Var = A | B | C | D
  deriving (Show, Eq, Ord, Generic, Data, Typeable)
data Expr = Lambda Var Expr | App Expr Expr | Var Var | Hole
  deriving (Show, Eq, Ord, Generic, Data, Typeable)
instance SOP.Generic Var
instance SOP.HasDatatypeInfo Var
instance SOP.Generic Expr
instance SOP.HasDatatypeInfo Expr
instance Shaped Expr
instance Shaped Var
instance NFData Var
instance NFData Expr
instance Arbitrary Var where
   arbitrary = genericArbitrary uniform
   -- shrink = genericShrink
instance Arbitrary Expr where
   arbitrary = genericArbitraryRec (1 G.% 1 G.% 0 G.% 0 G.% ()) `withBaseCase` oneof [fmap Var arbitrary, pure Hole]
   shrink = genericShrink


-- >>> prettyWithKey $ indexTerm (1::Int, "abc")
-- "0#(,) 1#1 2#(3#'a' : 4#5#'b' : 6#7#'c' : 8#[])"

instance Shaped a => Plated (WithKey % (BTree a)) where
 plate f (Wrap (WithKey k a0)) = Wrap . WithKey k <$> traverseShape f a0
traverseShape :: forall a f. (Shaped a, Applicative f) => (WithKey % (BTree a) -> f (WithKey % (BTree a))) -> Shape (BTree a) ((%) WithKey) -> f (Shape (BTree a) ((%) WithKey))
traverseShape f a = match @(BTree a) a a (\x _ -> unflatten <$> traverseFlattened @Shaped (maybeF f) x)
maybeF :: forall t p f. (Typeable p, Typeable t, Applicative f) => (p -> f p) -> t -> f t
maybeF f a = case eqT @p @t of
  Just Refl -> f a
  Nothing -> pure a
indexTerm :: Shaped a => a -> WithKey % a
indexTerm = fst . indexTermFrom 0

indexTermFrom :: Shaped a => Int -> a -> (WithKey % a, Int)
indexTermFrom i0 = flip runState i0 . sequenceInterleaved distributeLaw . interleave inj
  where
    inj a = Comp $ do
       s <- get :: (State Int Int)
       put (s+1)
       pure (WithKey s a)
    distributeLaw :: Functor f => WithKey (f a) -> f (WithKey a)
    distributeLaw (WithKey i a) = fmap (WithKey i) a

sequenceInterleaved :: forall a f g. (Shaped a, Monad f, Functor g) => (forall y. g (f y) -> f (g y)) -> (f :.: g) % a -> f (g % a)
sequenceInterleaved distributeLaw a = getComp (fold step a)
  where
    step :: forall x. (Shaped x, Monad f, Functor g) => (f :.: g) (Shape x (f :.: (%) g)) -> (f :.: ((%) g)) x
    step (Comp t) = Comp (doIt t)
      where
        doIt :: (f (g (Shape x (f :.: (%) g)))) -> (f (g % x))
        doIt = doWrap . doJoin . doUnwrap

        doUnwrap :: f (g (Shape x (f :.: (%) g))) -> f (g (f (Shape x ((%) g))))
        doUnwrap = fmap (fmap (splitF @x))

        doJoin :: f (g (f h)) -> f (g h)
        doJoin f =  join (fmap distributeLaw f)

        doWrap :: f (g (Shape x ((%) g))) -> f (g % x)
        doWrap = fmap Wrap
    getComp (Comp x) = x

splitF :: forall a f g. (Shaped a, Applicative f) => Shape a (f :.: g) -> f (Shape a g)
splitF d = match @a d d $ \flat _ ->
  fmap unflatten $ traverseFlattened @Top (\(Comp x) -> x) flat

data WithKey a = WithKey { getKey :: Int, value :: a }
  deriving (Show, Eq, Ord, Generic, Data, Typeable, Functor, Traversable, Foldable)

getValueFromInterleaved :: Shaped a =>WithKey % a -> a
getValueFromInterleaved  = fuse value

data SomeTyp f where
   SomeTyp :: (Shaped a) => f % a -> SomeTyp f
unBox :: forall a f. (Typeable f, Typeable a) => SomeTyp f -> Maybe (f % a)
unBox (SomeTyp a) = cast a
boxTyp :: SomeTyp f -> TypeRep
boxTyp (SomeTyp @a _) = typeRep (undefined :: proxy a)
forceBox :: forall a f. (Typeable f, Typeable a) => SomeTyp f -> (f % a)
forceBox = fromJust . unBox

{-# INLINE overChildren #-}
overChildren :: forall f g. (Typeable f, Applicative g, Traversable f) => LensLike' g (SomeTyp f) (SomeTyp f)
overChildren f (SomeTyp @a (Wrap fa)) = fmap (SomeTyp @a . Wrap) $ sequenceA $ (\a -> match @a a a $ \flat _ -> worker flat) <$> fa
  where
    worker :: (All Shaped xs, Applicative g) => Flattened (Shape a) ((%) f) xs -> g (Shape a ((%) f))
    worker (Flattened rebuild xs) = rebuild <$> go xs
    go :: All Shaped xs => NP ((%) f) xs -> g (NP ((%) f) xs)
    go cs = case cs of
      Nil -> pure Nil
      (:*) @_ @_ @c x xs -> liftA2 (\a b -> forceBox @c a :* b) (f (SomeTyp x)) (go xs)

boxed :: forall a f. (Typeable f, Shaped a) => Lens' (f % a) (SomeTyp f)
boxed f a = fmap (forceBox @a) $ f (SomeTyp a)


  -- unflatten $ mapFlattened @Shaped undefined flat
-- step :: f g (Shape x (f ((%) g))) -> f ((%) g) x
-- step = _

    
    
       
instance HasIdx (WithKey a) Int where
  theIdx = getKey
instance (HasIdx (SomeTyp f) o, forall a. HasIdx (f a) o) => HasIdx (SomeTyp f) o where
  theIdx (SomeTyp (Wrap f)) = theIdx f
    
-- myShrinker :: (MonadCritical Int m, MonadSnapshot m, MonadVar m, MonadGraphMut Int m, Alternative m, MonadOracle m, RecView (SomeTyp WithKey) m, MonadCut m) => m Bool
-- myShrinker = doShrink $ replaceNode (\k -> tryReplace k Hole) childExpr

data BTree a = Leaf a | Node (BTree a) (BTree a)
  deriving (Show, Eq, Ord, Generic, Data, Typeable, Foldable, Functor)
newtype NoShrink a = NoShrink {unNoShrink :: a}
  deriving (Eq, Ord, Show, Num, Enum)
instance Arbitrary (NoShrink a) where
    arbitrary = undefined
    shrink _ = []
instance Arbitrary (BTree a) where
    arbitrary = undefined
    shrink = coerce .  genericShrink . fmap NoShrink
instance SOP.Generic (BTree a)
instance SOP.HasDatatypeInfo (BTree a)
instance Shaped a => Shaped (BTree a)
toTree :: [a] -> BTree a
toTree ls = case ls of
  [] -> error "toTree: empty list"
  [a] -> Leaf a
  _ -> Node (toTree a) (toTree b)
  where
    (a,b) = splitAt (length ls `div` 2) ls
shrinkTest2 = print . head . dropWhile ((==False) . fst) . reverse $ fmap (fmap prettyWithKey) $ traceForest (testP . getValueFromInterleaved) $  myShrinkList
instance HasIdx (WithKey % a) Int where
    theIdx (Wrap f) = theIdx f

myShrinkList :: RoseForestT Identity (WithKey % BTree Int)
myShrinkList = runShrinkForest t $ evalCriticalT @Int $ runGraphT $ runVarTFrom i $ do
  cut $ do
    let
        childExpr :: Traversal' (WithKey % BTree Int) (WithKey % BTree Int)
        childExpr = plate
    recursive $ do
        d <- depsMap childExpr
        addDeps d
        let
          theShrinker = (replaceNode (\_ -> injectVal (Leaf 0)) childExpr)
          -- otherChrinker =  <> 
          -- loop = do
          --   doShrink theShrinker >>= \case
          --     True -> loop
          --     False -> pure ()
        -- loop
        smartLoop theShrinker
        traceM "THIS IS THE SECOND PART"
        smartLoop (hoistNode childExpr <> (hoistInCrit childExpr))
        -- traceM "THIS IS THE THRID PART"
        -- smartLoop 
        -- traceM "THIS IS THE THIRD PART"
        -- smartLoop (hoistInCrit childExpr)
        traceM ("OUTPUT COUNT " <> (show $ unsafePerformIO getTracker))
        pure ()
        crits <- getCriticals
        traceM ("criticals " <> (compact crits))
        hidden <- getHidden
        traceM ("hidden " <> (compact hidden))
  where (t, i) = indexTermFrom 0 (toTree [0..1000])


-- testP :: (Ord a, Num a, Foldable t) => t a -> Bool
-- testP x = pushTracker (out, length x) out
--   where out = S.null $ foldr S.delete (S.fromList  [100,200,300,400,500,600,700,800,900]) x

testP' :: (Ord a, Num a, Foldable t, Enum a) => a -> t a -> Bool
testP' a x = pushTracker (out, length x) out
  where out = S.isSubsetOf (S.fromList ([a..a+9])) (S.fromList (F.toList x))
testP :: (Show (t a), Ord a, Show a, Num a, Foldable t, Enum a) => t a -> Bool
testP x = pushTracker (out, length x) out
  where
    out = S.isSubsetOf (S.fromList ([100,200,300,400,500,600,700,800,900])) (S.fromList (F.toList x))
    -- !_ = trace (show x) ()
    


-- myShrinkTree :: RoseForestT Identity (WithKey % Expr)
-- myShrinkTree = runShrinkForest idxExpr $ evalCriticalT @Int $ runGraphT $ runVarTFrom i $ do
--   downwardM boxed $ do
--     recursive $ do
--         checkpoint
--         d <- depsMap childExpr
--         addDeps d
--         let
--           loop = do
--             myShrinker >>= \case
--               True -> loop
--               False -> pure ()
--         loop
--         -- shrinkTree childExpr (\k -> tryReplace k (Var A))
--         -- s <- getCriticals
--         pure ()
--   where
--     (idxExpr, i) = indexTermFrom 0 expr
-- childExpr :: (Typeable f1, Applicative f2, Traversable f1) => (SomeTyp f1 -> f2 (SomeTyp f1)) -> SomeTyp f1 -> f2 (SomeTyp f1)
-- childExpr = overChildren . filtered (\x -> boxTyp x == typeRep (undefined :: proxy Expr))

--         -- let nav k = navigator (flipChildren deps) overChildren k
--         -- traceM (show deps)
--         -- nav 2
--         -- c <- cursors (fmap prettyWithKey . unBox @Var)
--         -- traceM (show  c)
--         -- nav 7
--         -- c <- cursors (fmap prettyWithKey . unBox @Var)
--         -- traceM (show  c)
--         -- up
--         -- c <- cursors (fmap prettyWithKey . unBox @Expr)
--         -- traceM (show  c)
--         -- pull rightward
--         -- c <- cursors (fmap prettyWithKey . unBox @Expr)
--         -- traceM (show  c)
      
--       -- navigateTo 

injectVal :: (MonadVar m, MonadZipper (WithKey % o) m, Shaped o) => o ->  m (WithKey % o)
injectVal b = do
    i <- mkVar
    let (b', i') = indexTermFrom i b
    setVar i'
    pure b'

tryReplace :: forall a m. (Show a, Alternative m, MonadVar m, Shaped a, Eq a) => SomeTyp WithKey -> a -> m (SomeTyp WithKey)
tryReplace z@(SomeTyp @b a) b = case Typ.eqT @a @b of 
  Just Refl -> do
    -- traceM ("replacing " <> prettyWithKey a <> " with " <> show b)
    do
        i <- mkVar
        let (b', i') = indexTermFrom i b
        setVar i'
        pure $ SomeTyp @a b'
  Nothing -> empty
unWrap :: (f % a) -> f (Shape a ((%) f))
unWrap (Wrap a) = a

expr :: Expr
-- expr = z4 -- Lambda A (App (Lambda B (Lambda A (App (Lambda D (Var C)) (Lambda A (Var C))))) (Lambda A (App (App (Lambda D (Var B)) (Lambda B (Var C))) (Lambda A (App (Var B) (Var C))))))
--   where
--     vd = Var D
--     z4 = App z3 z3
--     z3 = App z2 z2
--     z2 = App z1 z1
--     z1 = App vd vd
-- expr = App (Var D) (App (Var B) (Var C))
expr = App (App (Lambda D (App (App (Lambda C (Var D)) (Lambda A (Var B))) (Lambda C (App (Var A) (Var A))))) (Lambda A (App (App (App (Var A) (Var A)) (Lambda A (Var D))) (App (Lambda B (Var A)) (App (Var C) (Var D)))))) (Lambda C (App (App (Lambda A (Lambda A (Var C))) (Lambda A (App (Var D) (Var C)))) (Lambda B (Lambda B (App (Var B) (Var C))))))
size :: Expr -> Int
size (Lambda _ e) = 1 + size e
size (App e1 e2) = 1 + size e1 + size e2
size _ = 1
propLam :: Expr -> Bool
propLam lam = case eval' lam of
  Nothing -> False
  Just o -> size o <= size lam

shrinkWith2 :: Arbitrary t => (t -> Bool) -> t -> t
shrinkWith2 p e0 = go 0 e0 (shrink e0)
  where
    go _ e [] = e
    go i e (x:xs) = if p x then go i x (delayBads i (shrink x)) else go (i+1) e xs

    delayBads i ls = case splitAt i ls of
      (a,b) -> b ++ a

shrinkWith :: Arbitrary t => (t -> Bool) -> t -> t
shrinkWith p e0 = go e0 (shrink e0)
  where
    go e [] = e
    go e (x:xs) = if p x then go x (shrink x) else go e xs

qsShrink :: Arbitrary t => (t -> Bool) -> t -> t
qsShrink p e0 = shrinkWith (isNothing . join . teaspoon . briefly . p) e0
     
    

eval' :: Expr -> Maybe Expr
eval' = briefly . eval mempty

briefly :: NFData p => p -> Maybe p
briefly x = unsafePerformIO $ fmap (x <$) $ timeout 500000 (x `deepseq` doSomething)

{-# NOINLINE doSomething #-}
doSomething :: IO ()
doSomething = do
  return ()

eval :: M.Map Var Expr -> Expr -> Expr
eval e0 s0
  -- | trace ("eval " ++ show s0) False = undefined
  -- | snd $ incCount (s0, False) = undefined
  |otherwise = go e0 s0
  where
    go e (Var v) = M.findWithDefault (Var v) v e
    go e (App a b) = case go e a of
        Lambda v x -> eval (M.insert v b e) x
        a' -> App a' b
    go _ a = a

repeatedTests :: IO ()
repeatedTests = do
   let
     go x
       | x > 990 = pure []
     go i = do
        modifyIORef myTracker (\_ -> [])
        deepseq (length $ shrinkWith2 (testP' i) (fmap NoShrink [0..1050::Int])) (pure())
        o <- getTracker
        let len = length o
        let total = sum (map snd o)
        os <- go (i+1)
        pure ((unNoShrink i,total,len) : os)
   print =<< go 0

{-# NOINLINE myTracker #-}
myTracker :: IORef [(Bool, Int)]
myTracker = unsafePerformIO $ newIORef []

{-# INLINE pushTracker #-}
pushTracker :: (Bool, Int) -> a -> a
pushTracker s a = unsafePerformIO (modifyIORef' myTracker (s:)) `seq` a
getTracker :: IO [(Bool, Int)]
getTracker = readIORef myTracker


propWorks :: Expr -> Bool
propWorks e = eval mempty e `seq` True


test :: IO ()
test = quickCheck propLam
-- prop>>> propWorks
--

prettyWithKey :: (Shaped t) => (WithKey % t) -> String
prettyWithKey d = showPrettyFieldS False "_" 0 (renderfold d) ""
-------------------------------
-- Pretty-printing demands --
-----------------------------

-- | A very general 'showsPrec' style function for printing demands
--
-- @showPrettyFieldS q t p r@ returns a function @(String -> String)@ which
-- appends its input to a pretty-printed representation of a demand.
--
-- Specifically:
-- * @q@ is a boolean flag determining if names should be printed
-- as qualified
-- * @t@ is a string which is to be printed when a thunk is encountered
-- * @p@ is the precedence context of this function call
-- * @r@ is the 'Rendered Thunk' representing some demand
--
-- This is very general, but we expose it in its complexity just in case some
-- person wants to build a different pretty-printer.
--
-- The precedence-aware pretty-printing algorithm used here is adapted from a
-- solution given by Brian Huffman on StackOverflow:
-- <https://stackoverflow.com/questions/27471937/43639618#43639618>.
showPrettyFieldS
  :: Bool -> String -> Int -> Rendered WithKey -> String -> String
showPrettyFieldS qualifyNames t prec (RWrap (WithKey k pd)) =
  shows k . ('#':) . case pd of
    ConstructorD name fields ->
      showParen (prec > 10 && length fields > 0) $
        showString (qualify name)
        . flip foldMapCompose fields
          (((' ' :) .) . showPrettyFieldS qualifyNames t 11)
    RecordD name recfields ->
      showParen (prec > 10) $
        showString (qualify name)
        . flip foldMapCompose recfields
          (\(fName, x) ->
             ((((" " ++ qualify fName ++ " = ") ++) .) $
             showPrettyFieldS qualifyNames t 11 x))
    InfixD name assoc fixity l r ->
      showParen (prec > fixity) $
        let (lprec, rprec) =
              case assoc of
                LeftAssociative  -> (fixity,     fixity + 1)
                RightAssociative -> (fixity + 1, fixity)
                NotAssociative   -> (fixity + 1, fixity + 1)
        in showPrettyFieldS qualifyNames t lprec l
         . showString (" " ++ qualify name ++ " ")
         . showPrettyFieldS qualifyNames t rprec r
    CustomD fixity list ->
      showParen (prec > fixity) $
        foldr (.) id $ flip fmap list $
          extractEither
          . bimap (showString . qualifyEither)
                  (\(f, pf) -> showPrettyFieldS qualifyNames t f pf)
  where
    qualify (m, _, n) =
      if qualifyNames then (m ++ "." ++ n) else n

    qualifyEither (Left s) = s
    qualifyEither (Right (m, n)) =
      if qualifyNames then (m ++ "." ++ n) else n

    extractEither (Left x)  = x
    extractEither (Right x) = x

    foldMapCompose :: (a -> (b -> b)) -> [a] -> (b -> b)
    foldMapCompose f = appEndo . foldMap (Endo . f)
