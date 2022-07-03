{-| Incremental topo sort -}
{-# LANGUAGE OverloadedLabels #-}
module EGraph.Pending where
import qualified Data.Set as S
import qualified Data.Map as M
import GHC.Generics (Generic)
import Control.Monad.State
import Optics
import Optics.State.Operators ((.=), (?=))
import Data.Maybe (catMaybes)
data Pending a = Pending {
   -- | How many children are unknown - when this becomes 0, propagate.
   -- When a child occurs multiple times it only counts once
   unknownChildren :: M.Map a Int,
   -- | Backmap of children to parents
   occursIn :: M.Map a (S.Set a)
} deriving (Eq, Ord, Show, Generic)


mkPending :: Ord a => M.Map a (S.Set a) -> Pending a
mkPending argMap = Pending childCounts revMap
  where
    childCounts = M.map S.size argMap
    revMap = M.fromListWith S.union $ do
      (parent, children) <- M.toList argMap
      child <- S.toList children
      return (child, S.singleton parent)

-- | Set the 'learned' elements as known, and propagate.
-- Returns the set of elements that were learned by propagation
-- The original 'learned' is part of the input if they weren't done before
markKnown :: Ord a => [a] -> Pending a -> (S.Set a, Pending a)
markKnown learned s = execState (go learned) (mempty, s)
  where
    go :: Ord a => [a] -> State (S.Set a, Pending a) ()
    go [] = pure ()
    go (x:xs) = do
      alreadyMarked <- gets (has $ _1 % at x)
      if alreadyMarked
      then go xs
      else do
        modify $ _1 % at x .~ Just ()
        occurences <- use (_2 % #occursIn % at x % non mempty)
        left <- forM (S.toList occurences) $ \occ -> do
            i <- use (_2 % #unknownChildren % at occ)
            case i of
              Nothing -> pure Nothing
              Just 1 -> do
                _2 % #unknownChildren % at occ .= Nothing
                pure $ Just occ
              Just n -> do
                _2 % #unknownChildren % at occ ?= (n-1)
                pure Nothing
        go (catMaybes left <> xs)
