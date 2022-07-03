{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, DerivingStrategies #-}
{-# LANGUAGE DeriveAnyClass #-}
module EGraph.Types where
import GHC.Generics (Generic)
import Data.Hashable (Hashable)

newtype Id = Id Int
  deriving stock Generic
  deriving newtype (Eq, Ord, Show, Hashable)
newtype Symbol = Symbol Int
  deriving stock Generic
  deriving newtype (Eq, Ord, Show, Hashable)
newtype Var = Var Int
  deriving stock Generic
  deriving newtype (Eq, Ord, Show, Hashable, Num)

data Elem' a = Elem {fSymbol :: Symbol, argIds :: [a]}
  deriving stock (Eq, Ord, Show, Generic)
  deriving anyclass (Hashable)

type Elem = Elem' Id

newtype RExp = RExp (Elem' RExp)

newtype Pat = Pat (Elem' (Either Var Pat))
  deriving Show

