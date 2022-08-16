module Obsolete.IndexedWalk where
-- | See IndexADT
import Prelude hiding ((*>), (>>=))
import qualified Prelude as P



newtype With l r m a = W { unW :: m a}

infixl 4 >>
(>>) :: Applicative f => With l m f x -> With m r f o -> With l r f o
(>>) l r = W ( unW l P.*> unW r)
infixl 4 *>
(*>) :: Applicative f => With l m f x -> With r m f o -> With l r f o
(*>) l r = W ( unW l P.*> unW r)
infixl 1 >>=
(>>=) :: Monad f => With l m f a -> (a -> With m r f b) -> With l r f b
(>>=) l r = W ( unW l P.>>= unW . r)

pure :: Applicative f => a -> With l l f a
pure = W . P.pure

lift :: m a -> With l l m a
lift = W

