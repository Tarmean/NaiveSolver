{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE LambdaCase #-}
module EGraph.Class where
import qualified Data.Vector.Unboxed as VU
import Control.Monad.State
import EGraph.Storage hiding (Symbol)
import Control.Lens
import Data.Generics.Labels ()
import qualified Data.IntMap.Strict as M
import EGraph.PlanTypes (Symbol (..))


type Prefix = VU.Vector Int
type Match = VU.Vector Int
type ClassId = Int
data MatchKind = Old | New | Both
class Monad m => MonadEgg m where
    -- TODO: Mix this with arbitrary indexing rather than reyling on prefixes
    forMatches :: MatchKind -> ClassId -> Symbol -> Prefix -> (Match -> m ()) -> m ()
    forClasses :: (ClassId -> m ()) -> m ()
    resolve :: Symbol -> Match -> m (Maybe ClassId)


instance MonadEgg m => MonadEgg (StateT s m) where
    resolve s m = lift (resolve s m)
    forMatches mk cid sym pref cb = StateT $ \s -> (,s) <$> forMatches mk cid sym pref (\x -> evalStateT (cb x) s)
    forClasses cb = StateT $ \s -> (,s) <$> forClasses  (\x -> evalStateT (cb x) s)

instance Monad m => MonadEgg (RebuildT m) where
    resolve (Symbol s) m = useEgg (resolveE s m)
    forMatches _ cid (Symbol sym) prefix cont = do
        let
          goWith (Just t) = mapM_ cont (lookupRange t prefix)
          goWith Nothing = pure ()

        m <- useEgg $ preuse (#classes . ix cid . #tables . ix sym)
        goWith m
    forClasses cont = do
        m <- useEgg (use #classes)
        mapM_ cont (M.keys m)
