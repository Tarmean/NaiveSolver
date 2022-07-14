--{-# Language DeriveGeneric #-}
--{-# LANGUAGE OverloadedLabels #-}
--{-# LANGUAGE LambdaCase #-}
--{-# LANGUAGE NamedFieldPuns #-}
--{-# OPTIONS_GHC -Wno-name-shadowing #-}
--{-# LANGUAGE FlexibleContexts #-}
--{-# LANGUAGE RecordWildCards #-}
module EGraph.Matching where

--import Data.List ( sort, maximumBy )
--import Data.Foldable (traverse_)
--import Data.Either (isLeft, isRight)
--import Data.Ord (comparing)
--import Data.Containers.ListUtils (nubOrdOn)
--import GHC.Generics (Generic)
--import qualified Data.Set as S
--import qualified Data.Map as M
--import Optics
--import Control.Monad.State

---- Egraph pattern compilation based on subgraph
---- isomorphism algs.
---- Compiles pattern into a vm to execute, this is a bit more sophisticated than what Egg does:
---- - We retrieve nodes whose arguments we have from the congruence closure hashtable
---- - If we bound a variable early we can check it eagerly 
---- - Our VM can get the classid id of our 'cursor', i.e. the node we are currently matching against. Useful for cyclic and multi-patterns (which Egg doesn't support).
---- - Checking back-edges may only require the class_id without knowing (yet) what tuple it could resolve to. But being able to refer to the id of tuples is generally useful:
----     'x? + ?a \in ?x => ?a \in 0'
----     for class in egg.search_sym(+):
----       if l.id == l.args[0]:
----          egg.queue_unify(l.args[1], egg.get(0))
----
----  Though in praxis we would prefer using an index or prefix for all known variables:
----
----     for clazz in egg.classes(+):
----       for l in egg.search(clazz, +, prefix: [clazz]):
----          egg.queue_unify(l.args[1], egg.get(0))
----
---- Non-index matching prefixes aren't implemented yet.
----
---- (Old) FIXME: check soundness hole when less tired
----
---- Problem:
----
---- f(h(x), g(h(x)))
----
---- check f.2 == g(f.1)
---- f.1 -> h

--import PureEgg (EGraph (..), Class (elems))
--import EggTypes
--import GHC.Stack (HasCallStack)
--import Data.Set (singleton)

--type PElem = Elem' PId
--newtype PId = PId Int
--  deriving (Eq, Ord, Show)
--type Pos = Int


--data VMState = V { cls :: !Id, elm :: !Elem, t0 :: !Id, t1 :: !Id, t2 :: !Id, t3 :: !Id, o0 :: !Id, o1 :: !Id, o2 :: !Id}
--  deriving Show
--execVM :: EGraph -> [VM] -> [VMState]
--execVM egg = go vundef
--  where
--    vundef = V noid (Elem (Symbol (-1)) []) noid noid noid noid noid noid noid
--    noid = Id (-1)
--    go :: VMState -> [VM] -> [VMState]
--    go v [] = pure v
--    go v (SearchSym sym vm:cont) = do
--       cls <- index egg M.! sym
--       searchFrom v cls vm cont
--    go v (SearchClass loc vm:cont) = do
--       let cls = getState loc v
--       searchFrom v cls vm cont
--    go v (CheckCur pos loc:xs) = do
--       let cls = getState loc v
--       guard $ argIds (elm v) !! pos == cls
--       go v xs
--    go v (StoreCur pos loc:xs) = do
--       let cls = argIds (elm v) !! pos
--       let v' = setState loc cls v
--       go v' xs
--    go v (StoreSelf loc:xs) = do
--       let v' = setState loc (cls v) v
--       go v' xs
--    go v (LookupCls (Elem sym args) loc:xs) = do
--       let args' = map (`getState` v) args
--       case PureEgg.lookup egg M.!? Elem sym args' of
--         Nothing -> []
--         Just o -> go (setState loc o v) xs

--    searchFrom v cls VMM{..} xs = do
--       let arg' = map (`getState` v) queryPrefix
--       e <- elems (classes egg M.! cls)
--       guard $ fSymbol e == matchSym
--       guard $ and $ zipWith (==) (argIds e) arg'
--       go v{cls=cls, elm=e} xs

--    getState :: HasCallStack => Loc -> VMState -> Id
--    getState (OutL 0) = o0
--    getState (OutL 1) = o1
--    getState (OutL 2) = o2
--    getState (TempL 0) = t0
--    getState (TempL 1) = t1
--    getState (TempL 2) = t2
--    getState (TempL 3) = t3
--    getState l = error (show l)

--    setState :: HasCallStack => Loc -> Id -> VMState -> VMState
--    setState (OutL 0) a v  = v { o0 = a }
--    setState (OutL 1) a v  = v { o1 = a }
--    setState (OutL 2) a v  = v { o2 = a }
--    setState (TempL 0) a v  = v { t0 = a }
--    setState (TempL 1) a v  = v { t1 = a }
--    setState (TempL 2) a v  = v { t2 = a }
--    setState (TempL 3) a v  = v { t3 = a }
--    setState VoidL _ v = v
--    setState _ _ _ = undefined


--data Loc = OutL Int | TempL Int | VoidL
--  deriving (Eq, Ord, Show, Generic)
--data VM
--    = SearchClass Loc VMMatch    -- known class id -> elems that match filter
--    | SearchSym Symbol VMMatch   -- we don't know class id, but we know the symbol - usually top-level
--    | StoreCur Pos Loc           -- store slot of current elem in currently inspected element
--    | StoreSelf Loc              -- store class of current elem
--    | LookupCls (Elem' Loc) Loc  -- lookup class, using stored values as arguments. f(a,b,c) -> class lookup in egg
--    | CheckCur Pos Loc           -- 
--  deriving (Eq, Ord, Show, Generic)
--data OptState = OS { optCtx :: MatchCtx, known :: M.Map PId Loc, reqIds :: S.Set PId, optOut :: [VM], tempLocs :: Int, outLocs :: Int }
--  deriving (Eq, Ord, Show, Generic)
--data VMMatch = VMM { matchSym :: Symbol, queryPrefix :: [Loc], queryMatches :: PId }
--  deriving (Eq, Ord, Show, Generic)
--ensureLoaded :: PId -> State OptState Loc
--ensureLoaded i = do
--   use (#known . at i) >>= \case
--     Just o -> pure o
--     Nothing -> do
--       o <- use (#optCtx . #vertex . singular (ix i))
--       case o of
--         Left _ -> error "unloaded var requried"
--         Right (Elem s ls) -> do
--           ls' <- traverse ensureLoaded ls
--           loc <- genTempLoc
--           emit $ LookupCls (Elem s ls') loc
--           #known . at i ?= loc
--           pure loc
--genTempLoc :: State OptState Loc
--genTempLoc = do
--    o <- #tempLocs <<+= 1
--    pure $ TempL o
--genOutLoc :: State OptState Loc
--genOutLoc = do
--    o <- #outLocs <<+= 1
--    pure $ OutL o

--toVM :: Pat -> [VM]
--toVM pat =  optOut $ execState (traverse_ matchHead filts) (OS ctx mempty reqIds [] 0 0)
--  where
--    ctx = mkContext pat
--    filts = runCtx ctx
--    reqIds = S.fromList $ concatMap getReqId filts
--getReqId :: MatchFilter -> [PId]
--getReqId F{..} = concatMap matchId matchers <> concatMap matchId newMatchers <> knownPrefix <> [matches]
--  where
--    matchId (KnownClassAt _ _) = []
--    matchId (EqShallow _ i) = [i]
--    -- this one explicitely shouldn't be stored for later use
--    matchId (KnownClass _) = []
    

--matchHead :: MatchFilter -> State OptState ()
--matchHead f@F {..} = do
--  matcher <- toVMMatch f
--  use (#known . at matches) >>= \case
--    Nothing -> emit $ SearchSym hasSymb matcher
--    Just o -> emit $ SearchClass o matcher
--  traverse_ defVar newVars
--  -- defSelfShallow matches
--  traverse_ defShallow newShallows
--  traverse_ validateMatch matchers
--  traverse_ validateMatch newMatchers

    

--toVMMatch :: MatchFilter -> State OptState VMMatch
--toVMMatch F{..} = do
--    queryPrefix <- traverse ensureLoaded knownPrefix
--    pure $ VMM {matchSym = hasSymb, queryPrefix = queryPrefix, queryMatches = matches}
--validateMatch :: Matcher -> State OptState ()
--validateMatch (EqShallow p i) = do
--  loc <- use (#known . singular (ix i))
--  emit $ CheckCur p loc
--validateMatch (KnownClassAt p i) = do
--  loc <- ensureLoaded i
--  emit $ CheckCur p loc
--validateMatch (KnownClass i) = do
--  Elem s ls <- use (#optCtx . #vertex . singular (ix i . _Right))
--  ls' <- traverse ensureLoaded ls
--  use (#reqIds . at i) >>= \case
--    Nothing -> emit $ LookupCls (Elem s ls') VoidL
--    Just _ -> do
--      loc <- genTempLoc
--      emit $ LookupCls (Elem s ls') loc
--      #known . at i ?= loc
      
---- defSelfShallow :: PId -> StateT OptState Identity ()
---- defSelfShallow i = do
---- -- FIXME: Are there situations where we need to store self?
----    Usually we see the argument version first. Maybe in multi patterns?
----    We don't want to emit self if there is no consumer
---- -- - g(x(f(?a)), h(f(?a), ?c))
----    loc <- genTempLoc
----    emit $ StoreSelf loc
----    #known . at i ?= loc
    
--defShallow :: (ElemId, Pos) -> StateT OptState Identity ()
--defShallow (i, p) =
--  use (#reqIds . at i) >>= \case
--    Nothing -> pure ()
--    Just _ -> do
--      loc <- genTempLoc
--      emit $ StoreCur p loc
--      #known . at i ?= loc

--defVar :: (VarId, Pos) -> StateT OptState Identity ()
--defVar (i, p) = do
--  loc <- genOutLoc
--  emit $ StoreCur p loc
--  #known . at i ?= loc
  

--emit :: VM -> State OptState ()
--emit x = #optOut <>= [x]

--type ElemId = PId
--type VarId = PId
--data MatchCtx = Ctx {
--    vertex :: M.Map PId (Either VarId PElem),
--    freeVars :: M.Map PId (S.Set PId),
--    knownIds :: S.Set PId,
--    knownClass :: S.Set PId,
--    visited :: S.Set PId
-- }
--  deriving (Eq, Ord, Show, Generic)



--patTest :: Pat
--patTest = Pat $ Elem (Symbol 0) [Left 0, Right (Pat $ Elem (Symbol 1) [Left 0])]
--patTest2 :: Pat
--patTest2 = Pat $ Elem (Symbol 0) [Right (Pat $ Elem (Symbol 1) [Left 0]), Right (Pat $ Elem (Symbol 2) [Left 0])]

--patTest3 :: Pat
--patTest3 = Pat $ Elem (Symbol 0) [Right (Pat $ Elem (Symbol 1) []), Left 0]
--patTest4 :: Pat
--patTest4 = Pat $ Elem (Symbol 0) [Left 0, Right (Pat $ Elem (Symbol 1) [])]
--patTest5 :: Pat
--patTest5 = Pat $ Elem (Symbol 5) [Left 1, Right (Pat $ Elem (Symbol 3) [Left 1])]

--patTest6 :: Pat
--patTest6 = 
--  Pat (Elem (Symbol 6) [Right $ Pat (Elem (Symbol 7) [Left 0]), Right $ Pat (Elem (Symbol 8) [Right $ Pat (Elem (Symbol 7) [Left 0])])])
---- for x in egg.symbol(sym0):
----    for y in x.child(0, sym1, []):
----       out[0] = y[0]
----       if egg.lookup(sym2, [y[0]]):
----           yield out
----
----  for y in egg.symbol(sym1):
----    out[0] = y[0]
----    temp = egg.lookup(sym2, [y[0]])
----    if egg.lookup(sym0, [y.class, temp]):
----       yield out
----
----  for z in egg.symbol(sym2):
----    out[0] = y[0]
----    temp = egg.lookup(sym1, [y[0]])
----    if egg.lookup(sym0, [temp, z.class]):
----       yield out
--rateGuess :: MatchCtx -> MatchFilter -> Double
--rateGuess Ctx{knownClass} F{..}
--  = scale 0 2 0 3 (l knownPrefix)
--  + scale 0 2 0 2 (l newMatchers)
--  + scale 0 2 0 2 (l newShallows)
--  + scale 0 1 0 2 (l matchers)
--  + (if matches `S.member` knownClass then 1 else 0)
--  where l = fromIntegral . length


---- SOUNDNESS HOLE HERE (probably)
---- seperate
--newlyKnown :: MatchCtx -> (S.Set VarId, S.Set ElemId) -> S.Set PId
--newlyKnown Ctx{..} (learnedVars, newShallow) = fixEq addShallow newDeep S.\\ knownClass
--  where
--    newKnown = knownIds `S.union` learnedVars
--    newDeep = S.fromList [x | (x,v) <- M.toList freeVars,  not (v `isSubset` knownIds),  v `isSubset` newKnown]
--    isSubset sub sup = S.intersection sub sup == sub

--    addShallow s = S.union s $ S.fromList [k | (k,Right (Elem _ ls)) <- M.toList vertex, all (\x -> x `S.member` s || x `S.member` newShallow) ls]

--    fixEq f s 
--      | s == s' = s
--      | otherwise = fixEq f s'
--      where s' = f s

--type CtxM = State MatchCtx


---- FIXME: This entire code path is real complicated, break it into its own module and (hopefully) simplify
--getNext :: MatchCtx -> Maybe (NewlyKnown, MatchFilter)
--getNext ctx = case [(nn, buildCandidate ctx e nn)  | e <- getAdj ctx, let nn = newlyKnown ctx (learnedVars ctx e)  ] of
--  [] -> Nothing
--  xs -> Just $ maximumBy (comparing $ rateGuess ctx . snd) xs

--learnedVars :: MatchCtx -> ElemId -> (S.Set VarId, S.Set ElemId)
--learnedVars Ctx{..} i = (learnedVars, newShallows)
--  where
--    Right (Elem _ ls) = vertex M.! i
--    learnedVars = S.fromList $ filter isNewVar ls
--    isNewVar a = isLeft (vertex M.! a) && a `S.notMember` knownIds
--    newShallows = S.union knownClass (S.fromList ls)

--insertVisited :: ElemId -> MatchCtx -> MatchCtx
--insertVisited e Ctx{..} = Ctx{visited = S.insert e visited, ..}

--runCtx :: MatchCtx -> [MatchFilter]
--runCtx ctx = go [] ctx
--  where
--   go acc ctx = case getNext ctx of
--     Just (nn, f) -> go (f:acc) (stepCtx ctx f nn)
--     Nothing -> reverse acc


--stepCtx :: MatchCtx -> MatchFilter -> NewlyKnown -> MatchCtx
--stepCtx Ctx{..} F{..} nn = Ctx {knownIds = S.union nn knownIds, knownClass = S.union nn (S.union shallowSeen knownClass), visited = S.insert matches visited, ..}
--  where
--    shallowSeen = S.insert matches $ S.fromList $ map fst newShallows

--getAdj :: MatchCtx -> [ElemId]
--getAdj Ctx {..} = [i | (i, Right _) <- M.toList vertex, i  `S.notMember` knownIds, i `S.notMember` visited]

--type NewlyKnown = S.Set PId
--buildCandidate :: MatchCtx -> ElemId -> NewlyKnown -> MatchFilter
--buildCandidate Ctx {..} c learned 
--  = F sym (map snd filterPre) (checkKnownClasses <> checkShallowKnown <> checkCollisions) (checkLearnedArgs <> checkLearnedNonArgs) newVars newShallow c
--  where
--    Right (Elem sym ls) = vertex M.! c

--    isNewVar x = isLeft (vertex M.! x) && x `S.notMember` knownIds
--    isNewShallowExpr x = isRight (vertex M.! x) && x `S.notMember` knownIds && x `S.notMember` learned
--    checkKnownClasses = map (uncurry KnownClassAt) filterRest
--    checkLearnedArgs = map (uncurry KnownClassAt) learnedPos
--    checkLearnedNonArgs = map KnownClass $ S.toList $ S.filter isNotVar learned S.\\ (S.fromList (map snd learnedPos) `S.union` visited `S.union` S.singleton c)

--    (filterPre,filterRest) = splitAt filterInfix filterPos
--    filterPos = filter ((`S.member` knownIds) . snd) $ zip [(0::Int)..] ls
--    filterInfix = length $ takeWhile (uncurry (==)) $ zip [(0::Int)..] $ map fst filterPos

--    checkCollisions = concat [allEqArg i ys | (i, ys) <- M.toList sameGroups, length ys > 1 ]

--    checkShallowKnown = map (uncurry KnownClassAt) $ filter  (isShallowKnown . snd) $ zip [0..] ls
--    isShallowKnown s = (s `S.notMember` learned) && (s `S.notMember` knownIds)  && (s `S.member` knownClass) && isNotVar s

--    learnedPos = filter (checkLearned . snd) $ zip [(0::Int)..] ls
--    checkLearned s = s `S.member` learned && isNotVar s
--    isNotVar s = isRight (vertex M.! s)

--    newVars = nubOrdOn fst $ filter (isNewVar . fst) $ zip  ls [0..]
--    newShallow = nubOrdOn fst $ filter (isNewShallowExpr . fst) $ zip  ls [0..]


--    -- duplicate subterm in match
--    -- f(g(x), g(x))
--    -- we don't fully know g(x) yet (variable x is missing) but we can filter so the classes are equivalent
--    sameGroups = M.map sort $ M.filter ((>1) . length) $ M.fromListWith (<>) [(r,[l]) | (l,r) <- zip[0..] ls, r `S.notMember` knownIds, not (checkLearned r)]
--    allEqArg i (_:ps) = map (`EqShallow` i) ps
--    allEqArg _ [] = []

--scale :: (Ord a, Fractional a) => a -> a -> a -> a -> a -> a
--scale f t l h x = s' + f
--  where
--    x' = max l (min x h)
--    p = (x' - l) / (h - l)
--    s' = p * (t - f)

--ctxFreeVars :: [(Either Var PElem, PId)] -> M.Map PId (S.Set Var)
--ctxFreeVars m = out
--  where
--    out = M.fromList [(i, step ev) | (ev, i) <- m]
--    step (Left v) = singleton v
--    step (Right (Elem _ ts)) = mconcat (map (out M.!) ts)

--mkContext :: Pat -> MatchCtx
--mkContext p = Ctx defs freeVars known mempty mempty
--  where
--    (_, m0) = patToCtx p
--    freeVars = M.map (S.map toVarId) $ ctxFreeVars (M.toList m0)
--    defs = M.fromList $ map swap $ M.toList m0
--    swap (Left a,b) = (b,Left $ toVarId a)
--    swap (Right a,b) = (b,Right a)
--    toVarId v = m0 M.! Left v
--    known = S.fromList $ M.keys $ M.filter null freeVars

