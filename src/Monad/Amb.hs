{-| Basic non-determinism monad plus ability to register unwinding handlers. Useful for undoing changes to mutable state:

   x <- 1 <|> 2
   #count += x
   onFailure (#count -= x)
   ...

This works even if #count targets mutable memory. Operationally, both alternatives and unwinders are allocated on the heap most of the time, often forming a linked list of continuation pointers
- Marking the CPS functions as oneShot lets GHC optimize some of that away
- But on average this can still be much worse than a specific undo stack, like dancing links
- It's also more flexible, though, because we can use compound data-structures with sharing in unwinding handlers :)
- But we must be careful not to leak memory in unwinding handlers by laziness :/
 -}
module Monad.Amb where
import Control.Monad.State ( ap )
import Control.Applicative ( Alternative((<|>), empty) )

data Amb r m a = Amb { runAmb :: (a -> m r -> m r) -> m r -> m r }
  deriving Functor
instance Monad (Amb r m) where
  Amb m >>= f = Amb $ \onSucc onFail -> m (\a onFail' -> runAmb (f a) onSucc onFail') onFail
instance Applicative (Amb r m) where
  pure a = Amb $ \k e -> k a e
  (<*>) = ap
instance (Alternative m) => Alternative (Amb r m) where
  empty = Amb $ \_ _ -> empty
  Amb m <|> Amb n = Amb $ \onSucc onFail -> m onSucc (n onSucc onFail)

-- | Before backtracking, run the given action.
-- Used to undo mutation
onFailure :: (Alternative m) => m () -> Amb r m ()
onFailure m = Amb $ \onSucc onFail -> onSucc () (m *> onFail)
