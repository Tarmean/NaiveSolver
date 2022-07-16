{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
module EGraph.Class where
import qualified Data.Vector.Unboxed as VU
import Control.Monad.State
import EGraph.Storage hiding (Symbol)
import Control.Lens
import Data.Generics.Labels ()
import qualified Data.IntMap.Strict as M
import EGraph.Types (ONSymbol (..))
import EGraph.PlanTypes (Symbol (..))


type Prefix = VU.Vector Int
type Match = VU.Vector Int
type ClassId = Int
data MatchKind = Old | New | Both
class Monad m => MonadEgg m sym | m -> sym where
    -- TODO: Mix this with arbitrary indexing rather than reyling on prefixes
    forMatches :: MatchKind -> ClassId -> sym -> Prefix -> (Match -> m ()) -> m ()
    forClasses :: (ClassId -> m ()) -> m ()
    resolve :: Symbol -> Match -> m (Maybe ClassId)


instance MonadEgg m sym => MonadEgg (StateT s m) sym where
    resolve s m = lift (resolve s m)
    forMatches mk cid sym pref cb = StateT $ \s -> (,s) <$> forMatches mk cid sym pref (\x -> evalStateT (cb x) s)
    forClasses cb = StateT $ \s -> (,s) <$> forClasses  (\x -> evalStateT (cb x) s)

instance Monad m => MonadEgg (RebuildT m) ONSymbol where
    resolve (Symbol s) m = useEgg (resolveE s m)
    forMatches _ cid msym prefix cont = do
        let
          goWith (Just t) = mapM_ cont (lookupRange t prefix)
          goWith Nothing = pure ()
          appSym (OSymbol sym) = do
            m <- useEgg $ preuse (#classes . ix cid . #tables . ix sym)
            goWith m
          appSym (NSymbol sym) = do
            m <- preuse (#new_data . ix cid . ix sym)
            goWith m
          appSym (ONSymbol sym) = appSym (NSymbol sym) *> appSym (OSymbol sym)
        appSym msym
    forClasses cont = do
        m <- useEgg (use #classes)
        mapM_ cont (M.keys m)
