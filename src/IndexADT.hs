{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QualifiedDo #-}
-- Sketch for a type-safe api that is obsoleted by zipper stuff
module IndexADT where
import qualified IndexedWalk as Ix
import GHC.Generics
import GHC.Types
import GHC.TypeLits

data (a::[Type]) :=> (b::Type)

type family ListApp (a :: [k]) (b :: [k]) :: [k] where
    ListApp '[] a = a
    ListApp (x ': xs) ys = x ': (ListApp xs ys)
type family ListAlt (a :: [k]) (b :: [k]) :: [k] where
    ListAlt '[] a = a
    ListAlt xs _ = xs
type family ConsOf rep constr where
   ConsOf (M1 C ('MetaCons l _ _) a) l = ConsOf a l
   ConsOf (M1 C ('MetaCons l _ _) a) r = '[]
   ConsOf (a :*: b) l = ListApp (ConsOf a l) (ConsOf b l)
   ConsOf (a :+: b) l = ListAlt (ConsOf a l) (ConsOf b l)
   ConsOf (M1 _ _ a) l = ConsOf a l
   ConsOf U1 _ = '[]
   ConsOf V1 _ = '[]
   ConsOf (K1 _ c) _ = '[c]

type ConstructorOf c (s :: Symbol) = ConsOf (Rep c) s :=> c

-- these are unsafe because they change the type-level without the value level
-- These should be combined with the (lifted) value-level implementations

unsafeAssertConstructor ::  forall s c f. Applicative f => Ix.With c (ConstructorOf c s) f ()
unsafeAssertConstructor = Ix.W (pure ())

unsafeAssertType ::  forall c o f. Applicative f => Ix.With o c f ()
unsafeAssertType = Ix.W (pure ())

type family Index (n :: Nat) (ls :: [a]) :: a where
    Index 0 (x ': _) = x
    Index n (_ ': xs) = Index (n-1) xs

unsafeField :: forall (n :: Nat) args f r. Applicative f => Ix.With (args :=> r) (Index n args) f ()
unsafeField = Ix.W (pure ())
unsafeResult :: forall args f r. Applicative f => Ix.With (args :=> r) r f ()
unsafeResult = Ix.W (pure ())

unsafeLocal :: Ix.With l r f a -> Ix.With l l f a
unsafeLocal (Ix.W a) = Ix.W a

unsafeGet :: Ix.With l l f l 
unsafeGet = undefined

test :: (Monad f) => Ix.With l ('[] :=> String) f Char
test = Ix.do
    unsafeAssertType @String
    unsafeAssertConstructor @":"
    c <- unsafeLocal (unsafeField @0 Ix.*> unsafeGet)
    unsafeField @1
    unsafeAssertConstructor @"[]"
    Ix.pure c
