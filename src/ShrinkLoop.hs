{-# LANGUAGE FunctionalDependencies #-}
module ShrinkLoop where



class Monad m => MShrink k m | m -> k where
    remove :: k -> m ()
    
