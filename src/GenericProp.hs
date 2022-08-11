{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Turn tuples of propagators into propagators of tuples
-- Mostly obsolete because egraphs do it better
module GenericProp where



import Propagator
import Data.Generics.Product.Types
import Control.Lens hiding ((...))
import Data.Kind (Type)
import Types (Var, Val(..), PSemigroup (..), PMonoid (..), PLattice, (<||>), LatticeVal (..), (<**>), PContains, BoundedLattice (..), IsLit (..), RegularSemigroup (..), DD (..), top)
import GHC.Generics
import Range (Range, (...))
import qualified Data.Set as S
import Control.Monad.State
import Control.Monad.Except
import Data.Foldable (asum)
import qualified DecisionDiagram as D


class ShouldProp (a :: Type) (b :: Type) where
   shouldProp :: Bool
   shouldProp = False
type family Relevant (a::Type) (b::Type) :: Bool where
    Relevant (Range e) LessEqThan = 'True
    Relevant (Val Bool) LessEqThan = 'True
    Relevant (Range e) Plus  = 'True
    Relevant _ _ = 'False


type family ITE (p::Bool) (a :: k) (b::k) :: k where
   ITE 'True a _ = a
   ITE _ _ b = b
type family RelevantListG (a::k -> Type) (b::Type) (acc :: [Type]) :: [Type] where
    RelevantListG V1 _ acc = acc
    RelevantListG U1 _ acc = acc
    RelevantListG (K1 _ (ClauseSet x)) a acc = ITE (Relevant a x) (ClauseSet x : acc) acc
    RelevantListG (K1 _ _) _ acc = acc
    RelevantListG (M1 _ _ v) a acc = RelevantListG v a acc
    RelevantListG (l :*: r) a acc = RelevantListG l a (RelevantListG r a acc)
    RelevantListG (l :+: r) a acc = RelevantListG l a (RelevantListG r a acc)
type RelevantList a b = RelevantListG (Rep a) b '[]

type family ClauseListG (a::k -> Type) (acc :: [Type]) :: [Type] where
    ClauseListG V1 acc = acc
    ClauseListG U1 acc = acc
    ClauseListG (K1 _ (PropEnv x)) acc = x : acc
    ClauseListG (K1 _ _) acc = acc
    ClauseListG (M1 _ _ v) acc = ClauseListG v acc
    ClauseListG (l :*: r) acc = ClauseListG l (ClauseListG r acc)
    ClauseListG (l :+: r) acc = ClauseListG l (ClauseListG r acc)
type ClauseList a = ClauseListG (Rep a) '[]


class Monad m => PropAll (pending :: [Type]) (a :: Type) m where
    propAll :: m ()
instance Monad m => PropAll '[] (a :: Type) m where
    propAll = pure ()
    
instance (MonadState s0 m, HasType (PropEnv x) s0, PropClauseAll (RelevantList a x) x m, PropAll xs a m) => PropAll (x ': xs) (a :: Type) m where
    propAll = do
       d <- popDirty @x
       propForOne @x @a d
       propAll @xs @a

propForOne :: forall b t m ls. (ls ~ RelevantList t b, PropClauseAll ls b m) => S.Set Var -> m ()
propForOne s  = propClauseAll @ls @b s

class Monad m => PropClauseAll (ls :: [Type]) (t :: Type)  m where
   propClauseAll :: S.Set Var -> m ()
instance Monad m => PropClauseAll '[] (t :: Type)  m where
   propClauseAll _ = pure ()
instance (Monad m, PropClauseOne x t m, PropClauseAll xs t m) => PropClauseAll (x ': xs) (t :: Type)  m where
   propClauseAll s = doProp @x @t s *> propClauseAll @xs @t s
class PropClauseOne (l :: Type) (t :: Type)  m where
  doProp :: S.Set Var -> m ()
instance (HasType (PropEnv (Val Bool)) s0,HasType (PropEnv (Range Int)) s0, HasType (ClauseSet LessEqThan) s0, MonadState s0 m) => PropClauseOne (ClauseSet LessEqThan) s (ExceptT (S.Set Var) m)  where
  doProp dirty = do
    onStruct @(ClauseSet LessEqThan) dirty (lessEqThanProp @Int)
instance (HasType (PropEnv (Range Int)) s0, HasType (ClauseSet Plus) s0, MonadState s0 m) => PropClauseOne (ClauseSet Plus) s (ExceptT (S.Set Var) m)  where
  doProp dirty = do
    onStruct @(ClauseSet Plus) dirty (plusProp @(Range Int))

type TestType = ((PropEnv (Val Bool)),(PropEnv (Range Int)), ClauseSet Plus, ClauseSet LessEqThan)

emptyTest :: TestType
emptyTest = (emptyPropEnv, emptyPropEnv, mkClauseSet(S.singleton (Plus 1 2 3)), mkClauseSet(S.singleton (LessEqThan 5 3 1)))

class TryNormalize a where
    tryNormalize1 :: a -> Maybe a
instance PropAll (ClauseList a) a (ExceptT (S.Set Var) (StateT a Identity)) => TryNormalize a where
    tryNormalize1 a = case runState (runExceptT (propAll @(ClauseList a) @a :: ExceptT (S.Set Var) (StateT a Identity) ())) a of
      (Left _,_) -> Nothing
      (Right _,b) -> Just b
tryNormalize :: (TryNormalize a) => a -> Maybe a
tryNormalize a = tryNormalize1 =<< tryNormalize1 a


instance (PSemigroup a,PSemigroup b) => PSemigroup (a,b) where
  (<?>) (a,b) (e,f) = liftM2 (,) (a <?> e) (b <?> f)
instance (PMonoid a,PMonoid b) => PMonoid (a,b) where
  pempty = (pempty,pempty)
instance (PMonoid a, PMonoid b, PLattice a,PLattice b) => PLattice (a,b) where
  (<||>) (a,b) (e,f) = (a <||> e) <**> (b <||> f)
instance (TryNormalize (a,b,c,d), PSemigroup a,PSemigroup b, PSemigroup c, PSemigroup d) => PSemigroup (a,b,c,d) where
  (<?>) (a,b,c,d) (e,f,g,h) = tryNormalize =<< liftM4 (,,,) (a <?> e) (b <?> f) (c <?> g) (d <?> h)
instance (TryNormalize (a,b,c,d), PMonoid a,PMonoid b, PMonoid c, PMonoid d) => PMonoid (a,b,c,d) where
  pempty = (pempty,pempty,pempty,pempty)
instance (TryNormalize (a,b,c,d), PMonoid a,PMonoid b,PMonoid c,PMonoid d,PLattice a,PLattice b, PLattice c, PLattice d) => PLattice (a,b,c,d) where
  (<||>) (a,b,c,d) (e,f,g,h) = case (a <||> e) <**> (b <||> f) <**> (c <||> g) <**> (d <||> h) of
     IsBot -> IsBot
     IsTop -> IsTop
     Is ((((p),q),r),s) -> Is (p,q,r,s)
instance (BoundedLattice a, BoundedLattice b, BoundedLattice c, BoundedLattice d, PMonoid (a,b,c,d), PLattice (a,b,c,d), Eq (a,b,c,d)) => BoundedLattice (a,b,c,d) where
    bot = (bot,bot,bot,bot)
    isBot x = bot == x

injectClause :: forall s o. (PMonoid o, HasType (ClauseSet s) o, Ord s) => s -> o
injectClause s = pempty & typed @(ClauseSet s) %~ \x -> x { newClauses = S.insert s (newClauses x) }

     
instance (PMonoid a,PMonoid b,PMonoid c,PMonoid d, TryNormalize (a,b,c,d), RegularSemigroup a, RegularSemigroup b, RegularSemigroup c, RegularSemigroup d) => RegularSemigroup (a,b,c,d) where
  (==>) (a,b,c,d) (e, f, g, h) = (a ==> e, b ==> f, c ==> g, d ==> h)
  (==>?) (a,b,c,d) (e, f, g, h)
     | or [l1,l2,l3,l4] = Just (q,r,s,t)
     | otherwise = Nothing
    where
      (l1, q) = mk a e
      (l2, r) = mk b f
      (l3, s) = mk c g
      (l4, t) = mk d h
      mk x y = case x ==>? y of
         Nothing -> (False, top)
         Just z -> (True, z)

newtype Compound a = Compound { getCompound :: a } deriving (Eq,Ord,Show, PSemigroup, PLattice, PMonoid, RegularSemigroup, BoundedLattice, TryNormalize)

instance (v ~ Var,  HasType (PropEnv (Val Bool)) (a,b,c,d), Ord a, Ord b, Ord c, Ord d, BoundedLattice a, BoundedLattice b, BoundedLattice c, BoundedLattice d, TryNormalize(a,b,c,d), RegularSemigroup (a,b,c,d), Show(a,b,c,d), IsLit v d, IsLit v c, IsLit v b, IsLit v a) => IsLit v (a,b,c,d) where
  isL v = injectValue v (Val True)
  notL v = injectValue v (Val False)
  maxSplitVar (a,b,c,d) = maximum [maxSplitVar a, maxSplitVar b, maxSplitVar c, maxSplitVar d]
  splitLit v (a,b,c,d)
    | not (b1 || b2 || b3 || b4) = Nothing
    | otherwise = Just (ls,rs)
    where
      (b1,la,ra) = trySplit v a
      (b2,lb,rb) = trySplit v b
      (b3,lc,rc) = trySplit v c
      (b4,ld,rd) = trySplit v d

      ls = case la <**> lb <**> lc <**> ld of
         IsTop -> IsTrue
         IsBot -> IsFalse
         Is (((p,q),r),s) -> (Iff (p,q,r,s))
      rs = case ra <**> rb <**> rc <**> rd of
         IsTop -> IsTrue
         IsBot -> IsFalse
         Is (((p,q),r),s) -> (Iff (p,q,r,s))
  evalVar v (a,b,c,d) = asum [evalVar v a, evalVar v b, evalVar v c, evalVar v d]


-- class Propagate f m where
--     doProp :: f Var -> AProp f m s
-- class ForProps a where
--    forProps :: (forall p. DoProp p a =>  PropEnv p) -> m ()
trySplit :: IsLit v a => v -> a -> (Bool, LatticeVal a, LatticeVal a)
trySplit v x = case splitLit v x of
  Nothing -> (False, Is x,Is x)
  Just (a,b) -> (True, inj a, inj b)
  where
    inj IsTrue = IsTop
    inj IsFalse = IsBot
    inj (Iff y) = Is y
    inj _ = error "illegal if"

mkRange :: Int -> Int -> Int -> DD v TestType
mkRange v i j = Iff (injectValue v (i...j) :: TestType)



test1 :: DD Var TestType
test1 = D.ifte 1 (mkRange 2 3 10) (mkRange 2 1 5)

test2 :: DD Var TestType
test2 = Iff (injectClause (Plus 2 2 3 :: Plus))
