{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DefaultSignatures #-}
module Types where
import qualified Data.Set as S
import qualified Data.Map.Merge.Lazy as M
import qualified Data.Map.Strict as M
import Data.Maybe (isNothing)
import qualified Prettyprinter as P

main :: IO ()
main = print "bdd"

class PContains s where
   -- compareC a b == Just LT
   -- \forall x \in a. x \in b
   compareC :: s -> s -> Maybe Ordering
contains :: PContains a => a -> a -> Bool
contains a b = case compareC a b of
   Just LT -> True
   Just EQ -> True
   _ -> False
class POrd s where
   -- compareP a b == Just LT
   -- \forall x \in a. \forall y \in b. x <= y
   compareP :: s -> s -> Maybe Ordering
(<=?) :: POrd a => a -> a -> Bool
(<=?) a b = case compareP a b of
   Just LT -> True
   Just EQ -> True
   _ -> False
type Var = Int
data DD s
  = If Var s (DD s) (DD s)
  | IsTrue
  | Iff s
  | IsFalse
  deriving (Eq, Ord, Show)
class (Eq s, PMonoid s, RegularSemigroup s, PLattice s, Show s) => IsLit s where
  -- | construct `var=True`
  isL :: Var -> s
  -- | construct `var=False`
  notL :: Var -> s
  -- | largest unknown var
  maxSplitVar :: s -> Var
  -- | Conditions on variable, `split x s` return
  --     Just (s|x=True, s|x=False)
  -- if x occurs in s. Afterwards, the results shouldn't refer to x.
  -- This could be implemented via `<?>`, `maxSplitVar`, and `==>` but a more performant implementation might be possible
  splitLit :: Var -> s -> Maybe (DD s,DD s)
  -- Check if the variable is definitely True/False
  evalVar :: Var -> s -> Maybe Bool

-- | Partial meet of data, a AND b is true so union their info
class PSemigroup s where
    -- | laws: associative, commutative, idempotent
    (<?>) :: s -> s -> Maybe s
-- | Partial merging with default
class PSemigroup s => PMonoid s where
    -- | no information. neutral element of <?>, absorbing element of <||>
    pempty :: s

-- | Partial join of data, a OR b is true so intersect their info
class (PSemigroup s) => PLattice s where
    -- | laws: associative, commutative, idempotent
    -- usually not distributive over <?>, applying it early loses information
    -- (that's why we do case distinction via bdd)
    (<||>) :: s -> s -> LatticeVal s
data LatticeVal a = IsTop | IsBot | Is a
  deriving (Eq, Ord, Show, Functor)
(<**>) :: (PMonoid a, PMonoid b) => LatticeVal (a) -> LatticeVal b -> LatticeVal (a,b)
IsBot <**> _ = IsBot
_ <**> IsBot = IsBot
Is f <**> Is a = Is (f, a)
Is f <**> IsTop = Is (f, top)
IsTop <**> Is a = Is (top, a)
IsTop <**> IsTop = IsTop

-- | deduplicates information which is saved elsewhere
-- FIXME: i defined this ad-hoc because I needed the operation, but is this just heyting algebras?
class PSemigroup a => RegularSemigroup a  where
    -- | a ==> b returns the (ideally minimum) x such that
    --  (a ==> b) &&& a  == a &&& b
    --
    -- for bounded lattices:
    -- a ==> a = pempty
    -- a <&> (a ==> b) = a <&> b
    -- b <&> (a ==> b) = b
    -- c ==> (a <&> b) ~ (c ==> a) <&> (c ==> b), if <&> is defined
    (==>?) :: a -> a -> Maybe a
    default (==>?) :: (Eq a, PMonoid a) => a -> a -> Maybe a
    (==>?) a b = if out == top then Nothing else Just out
      where out = (a ==> b)
    (==>) :: a -> a -> a
    default (==>) :: PMonoid a => a -> a -> a
    (==>) l r = case l ==>? r of
       Just o -> o
       Nothing -> top
    {-# MINIMAL (==>?)|(==>) #-}
top :: PMonoid a => a
top = pempty
class (PMonoid s, PLattice s) => BoundedLattice s where
    bot :: s
    isBot :: s -> Bool
    (&&&) :: s -> s -> s
    a &&& b = case a <?> b of
      Nothing -> bot
      Just s -> s
    (|||) :: s -> s -> s
    a ||| b = case a <||> b of
       IsBot -> bot
       IsTop -> top
       Is s -> s

-- | more accurate than pseudoinverse in RegularSemigroup
-- (a <> x) <> inv a  = x
class PSemigroup a => InverseSemigroup a  where
    inv :: a -> a

getLatticeVal :: BoundedLattice a => LatticeVal a -> a
getLatticeVal IsBot = bot
getLatticeVal (Is a) = a
getLatticeVal IsTop = top
notBot :: PMonoid a => LatticeVal a -> Maybe a
notBot IsBot = Nothing
notBot (Is a) = Just a
notBot IsTop = Just top

newtype Val a = Val {unVal :: a}
  deriving (Eq, Ord, Show)
instance Eq a => PContains (Val a) where
    compareC a b
      | a == b = Just EQ
      | otherwise = Nothing
instance Eq a => POrd (Val a) where
    compareP a b
      | a == b = Just EQ
      | otherwise = Nothing
instance Eq a => PSemigroup (Val a) where
    (<?>) (Val a) (Val b) = if a == b then Just (Val a) else Nothing
instance (Eq a) => PLattice (Val a) where
    (<||>) (Val a) (Val b) = if a == b then Is (Val a) else IsTop
 
data PMap k v = PMap (M.Map k v)
  deriving (Eq, Ord, Show)
(??) :: (Ord k) => PMap k v -> k -> Maybe v
(??) (PMap m) k = M.lookup k m
instance (Ord k, PSemigroup v) => PSemigroup (PMap k v) where
    (<?>) (PMap m) (PMap m') = fmap PMap (joinMap m m')
joinMap :: (Ord k, PSemigroup c) => M.Map k c -> M.Map k c -> Maybe (M.Map k c)
joinMap m m' = case M.mergeA M.preserveMissing M.preserveMissing (M.zipWithAMatched both) m m' of
  Just o -> Just o
  Nothing -> Nothing
  where
    both _ x y = x <?> y
instance (Ord k, PSemigroup v) => PMonoid (PMap k v) where
    pempty = PMap M.empty

emptyPMap :: PMap k v
emptyPMap = PMap M.empty

instance (Ord k,  RegularSemigroup v) => RegularSemigroup (PMap k v) where
    (==>?) (PMap m') (PMap m)
      | M.null merged = Nothing
      | otherwise = Just (PMap merged)
      where merged = M.merge M.preserveMissing M.dropMissing (M.zipWithMaybeMatched (const (==>?))) m m'
instance Eq a => RegularSemigroup (Val a) where
    _ ==> r = r
    (==>?) (Val x) (Val y)
      | x == y = Nothing
      | otherwise = Just (Val y)



instance (Ord k, PLattice v) => PLattice (PMap k v) where
  (<||>) (PMap l) (PMap r) = fmap PMap (meetMap  l r)

meetMap :: (Ord k, PLattice c) => M.Map k c -> M.Map k c -> LatticeVal (M.Map k c)
meetMap l r = toIs $ M.mergeA M.dropMissing M.dropMissing (M.zipWithMaybeAMatched (\_ a b -> wrap $ a <||> b)) l r
    where
      wrap IsBot = Nothing
      wrap IsTop = Just Nothing
      wrap (Is a) = Just (Just a)
      toIs Nothing = IsBot
      toIs (Just a) = Is a

instance IsLit (PMap Var (Val Bool)) where
    isL v = PMap $ M.singleton v (Val True)
    notL v = PMap $ M.singleton v (Val False)
    maxSplitVar (PMap p) = case M.maxViewWithKey p of
      Nothing -> -1
      Just ((v,_),_) -> v
    splitLit v env
      | isNothing (evalVar v env) = Nothing
      | otherwise = Just (removeVar v True env, removeVar v False env)
    evalVar v env = fmap unVal $ env ?? v

removeVar :: IsLit s => Var -> Bool -> s -> DD s
removeVar v b s = case s <?> isV v b of
    Nothing -> IsFalse
    Just s' -> iffMaybe (isV v b ==>? s')
iff :: (Eq s, PMonoid s) => s -> DD s
iff a = if a == top then IsTrue else Iff a
iffMaybe :: Maybe s -> DD s
iffMaybe Nothing = IsTrue
iffMaybe (Just a) = Iff a

isV :: IsLit s => Var -> Bool -> s
isV v b = if b then isL v else notL v

instance (P.Pretty k, P.Pretty v) => P.Pretty (PMap k v) where
  pretty (PMap m) = P.braces $ P.sep  $ P.punctuate P.comma [ P.pretty "v" P.<> P.pretty k P.<+> P.pretty ":=" P.<+> P.pretty v| (k,v) <- M.toList m]
instance P.Pretty e => P.Pretty (Val e) where
  pretty (Val e) = P.pretty e
instance (Eq e, PMonoid e, P.Pretty e) => P.Pretty (DD e) where
  pretty a = case a of
    IsTrue -> P.pretty "True"
    IsFalse -> P.pretty "False"
    If x s y z 
      | s == top -> P.parens body
      | otherwise -> P.parens $ P.sep [P.pretty s, P.pretty "&&" P.<+> body]
      where body = P.align $ P.sep [P.pretty "v" P.<> P.pretty x, P.pretty "?" P.<+> P.pretty y , P.pretty ":" P.<+> P.pretty z]
    Iff s -> P.pretty s
