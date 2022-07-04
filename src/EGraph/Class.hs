{-# LANGUAGE TupleSections #-}
module EGraph.Class where
import qualified Data.Vector.Unboxed as VU
import Control.Monad.State
import EGraph.PlanTypes (Symbol)


type Prefix = VU.Vector Int
type Match = VU.Vector Int
type ClassId = Int
class Monad m => MonadEgg m where
    -- TODO: Mix this with arbitrary indexing rather than reyling on prefixes
    forMatches :: ClassId -> Symbol -> Prefix -> (Match -> m ()) -> m ()
    forClasses :: (ClassId -> m ()) -> m ()
    resolve :: Symbol -> Match -> m (Maybe ClassId)


instance MonadEgg m => MonadEgg (StateT s m) where
    resolve s m = lift (resolve s m)
    forMatches cid sym pref cb = StateT $ \s -> (,s) <$> forMatches cid sym pref (\x -> evalStateT (cb x) s)
    forClasses cb = StateT $ \s -> (,s) <$> forClasses  (\x -> evalStateT (cb x) s)
    

