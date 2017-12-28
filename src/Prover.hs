{-# LANGUAGE LambdaCase, DeriveFunctor, MultiWayIf #-}

module Prover where

import Prelude hiding (lookup)
import Data.Map (Map (..))
import qualified Data.Map as M
import Data.Set (Set (..))
import qualified Data.Set as S
import Data.List (sortOn, intercalate)
import Data.Foldable
import Data.Maybe
import Control.Monad.State.Strict
import Control.Exception
-- |
-- This is a connection logic prover for first order logic

-- I treat a funtion with no variables as a constant, and a predicate with no
-- variables as an atomic formula
newtype Var a = Var a deriving (Eq, Ord, Functor)
data Func a = Func a [Either (Var a) (Func a)] deriving (Eq, Ord)

data Formula a = Pred a [Either (Var a) (Func a)]
               | Not (Formula a)
               | Formula a `And` Formula a
               | Formula a `Or` Formula a
               | Formula a `Implies` Formula a
               | Forall (Var a) (Formula a)
               | Exists (Var a) (Formula a) deriving Eq

data Atomic a = Predicate a [Either (Var a) (Func a)]
              | Negated a [Either (Var a) (Func a)] deriving (Eq, Ord)

data Proof = Valid | Invalid deriving (Eq, Show)

instance (Show a) => Show (Formula a) where
    show (Pred p []) = show p
    show (Pred p ls) = show p ++ "(" ++ intercalate ", "
        (map (\case (Left x) -> show x; (Right x) -> show x) ls) ++ ")"
    show (Not f) = "~ " ++ show f
    show (f1 `And` f2) = "(" ++ show f1 ++ " & " ++ show f2 ++ ")"
    show (f1 `Or` f2) = "(" ++ show f1 ++ " | " ++ show f2 ++ ")"
    show (f1 `Implies` f2) = "(" ++ show f1 ++ " -> " ++ show f2 ++ ")"
    show (Forall var f) = "![" ++ show var ++ "]: " ++ show f
    show (Exists var f) = "?[" ++ show var ++ "]: " ++ show f

instance (Show a) => Show (Var a) where
    show (Var x) = show x

instance (Show a) => Show (Func a) where
    show (Func f []) = show f
    show (Func f ls) = show f ++ "(" ++ intercalate ", "
        (map (\case (Left x) -> show x; (Right x) -> show x) ls) ++ ")"

instance (Show a) => Show (Atomic a) where
    show (Predicate p []) = show p
    show (Predicate p ls) = show p ++ "(" ++ intercalate ", "
        (map (\case (Left x) -> show x; (Right x) -> show x) ls) ++ ")"
    show (Negated p []) = "~" ++ show p
    show (Negated p ls) = "~" ++ show p ++ "(" ++ intercalate ", "
        (map (\case (Left x) -> show x; (Right x) -> show x) ls) ++ ")"

-- to negation normal form
nnf :: Formula a -> Formula a
nnf (Pred p vars) = Pred p vars
nnf (Forall var f) = Forall var (nnf f)
nnf (Exists var f) = Exists var (nnf f)
nnf (f1 `And` f2) = nnf f1 `And` nnf f2
nnf (f1 `Or` f2) = nnf f1 `Or` nnf f2
nnf (f1 `Implies` f2) = nnf (Not f1) `Or` nnf f2
nnf (Not (Not f)) = nnf f
nnf (Not (Forall var f)) = Exists var (nnf (Not f))
nnf (Not (Exists var f)) = Forall var (nnf (Not f))
nnf (Not (f1 `And` f2)) = nnf (Not f1) `Or` nnf (Not f2)
nnf (Not (f1 `Or` f2)) = nnf (Not f1) `And` nnf (Not f2)
nnf (Not (f1 `Implies` f2)) = nnf f1 `And` nnf (Not f2)
nnf (Not f) = Not (nnf f)

-- Converts the predicates, functions on variables to int values.
-- All variables bound to a quantifier is given a unique number, even if the
-- same variable is used elsewhere. For example:
-- ![X]: (?[Y]: p(X,Y) & ?[Y]: p(Y,X)) will be converted to:
-- ![0]: (?[1]: 2(0,1) & ?[3]: 2(3,0))
mapInts :: Ord a => Formula a -> Formula Int
mapInts f = evalState (go M.empty f) (0, M.empty)
    where
        go :: Ord a => Map (Var a) Int -> Formula a -> State (Int, Map a Int) (Formula Int)
        go vars (Pred p xs) = do
           (varNum, preds) <- get
           case M.lookup p preds of
                Nothing -> do put (varNum + 1, M.insert p varNum preds)
                              xs' <- mapM (replaceVarOrFunc vars) xs
                              return $ Pred varNum xs'
                Just n -> do xs' <- mapM (replaceVarOrFunc vars) xs
                             return $ Pred n xs'
        go vars (Not f) = Not <$> go vars f
        go vars (f1 `And` f2) = liftM2 And (go vars f1) (go vars f2)
        go vars (f1 `Or` f2) = liftM2 Or (go vars f1) (go vars f2)
        go vars (f1 `Implies` f2) = liftM2 Implies (go vars f1) (go vars f2)
        go vars (Forall var f) = do
            varNum <- newVarNum
            f' <- go (M.insert var varNum vars) f
            return $ Forall (Var varNum) f'
        go vars (Exists var f) = do
            varNum <- newVarNum
            f' <- go (M.insert var varNum vars) f
            return $ Exists (Var varNum) f'

        replaceVarOrFunc :: Ord a => Map (Var a) Int
                                  -> Either (Var a) (Func a)
                                  -> State (Int, Map a Int) (Either (Var Int) (Func Int))
        replaceVarOrFunc vars (Left var) =
            return $ case M.lookup var vars of
                Nothing -> throw $! PatternMatchFail "Formula contains free variables!"
                Just n -> Left (Var n)
        replaceVarOrFunc vars (Right (Func name xs)) = do
            (varNum, preds) <- get
            case M.lookup name preds of
                Nothing -> do
                    put (varNum + 1, M.insert name varNum preds)
                    xs' <- mapM (replaceVarOrFunc vars) xs
                    return $ Right (Func varNum xs')
                Just n -> do
                    xs' <- mapM (replaceVarOrFunc vars) xs
                    return $ Right (Func n xs')

        newVarNum :: Ord a => State (Int, Map a Int) Int
        newVarNum = do
            (varNum, preds) <- get
            put (varNum + 1, preds)
            return varNum

-- Applies herbrandtiztion to a Formula. Assumes negated normal form, and that
-- every bound variable is unique.
--
-- It also removes all Exists quantifiers, since all formulas are implicitly
-- bound by an Exists quantifiers after the herbrandtisation, which could be
-- extracted to the front of the formula without changing the structure of the
-- formula; We do not remove any important information by removing them.
herbrandtisize :: Formula Int -> Formula Int
herbrandtisize f = evalState (go S.empty M.empty f) (findMax f)
    where
        go :: Set (Var Int) -- Existentially quantified variables
           -> Map (Var Int) (Func Int) -- Maps every Universially quantified variable to a unique function
           -> Formula Int -- input
           -> State Int (Formula Int) -- State of each new function variable
        go vars funcs (Pred p xs) = Pred p <$> mapM (replaceVarOrFunc funcs) xs
        go vars funcs (Not f) = Not <$> go vars funcs f
        go vars funcs (f1 `And` f2) = liftM2 And (go vars funcs f1) (go vars funcs f2)
        go vars funcs (f1 `Or` f2) = liftM2 Or (go vars funcs f1) (go vars funcs f2)
        go vars funcs (Forall var f) = do
            funcVar <- get
            put $ funcVar + 1
            let func = Func funcVar $ map Left $ toList vars
            go vars (M.insert var func funcs) f
        go vars funcs (Exists var f) = go (S.insert var vars) funcs f
        go _ _ _ = error "Not in negated normal form"

        replaceVarOrFunc :: Map (Var Int) (Func Int)
                         -> Either (Var Int) (Func Int)
                         -> State Int (Either (Var Int) (Func Int))
        replaceVarOrFunc funcs var@(Left v) = maybe (return var) (return . Right) $ M.lookup v funcs
        replaceVarOrFunc funcs (Right (Func f xs)) =
            Right . Func f <$> mapM (replaceVarOrFunc funcs) xs

findMax :: Formula Int -> Int
findMax (Pred n xs) = max n $ findMax' xs
    where
        findMax' = foldr (\case Left (Var x) -> max x
                                Right (Func f xs) -> max (max f $ findMax' xs)) 0
findMax (Not f) = findMax f
findMax (f1 `And` f2) = max (findMax f1) (findMax f2)
findMax (f1 `Or` f2) = max (findMax f1) (findMax f2)
findMax (f1 `Implies` f2) = max (findMax f1) (findMax f2)
findMax (Forall (Var v) f) = max v $ findMax f
findMax (Exists (Var v) f) = max v $ findMax f


-- Assumes the formula is herbrandtized
-- This is the standard translation into disjunctive normal form
dnf :: Show a => Formula a -> Formula a
dnf (Pred p xs) = Pred p xs
dnf (Not (Pred p xs)) = Not (Pred p xs)
dnf ((f1 `Or` f2) `And` f3) = dnf (f1 `And` f3) `Or` dnf (f2 `And` f3)
dnf (f1 `And` (f2 `Or` f3)) = dnf (f1 `And` f2) `Or` dnf (f1 `And` f3)
dnf (f1 `And` f2) =
    let f1' = dnf f1
        f2' = dnf f2
        isOr (_ `Or` _) = True
        isOr _ = False
    in  if isOr f1' || isOr f2' then dnf (f1' `And` f2') else f1' `And` f2'
dnf (f1 `Or` f2) = dnf f1 `Or` dnf f2
dnf _ = error "The formula is not herbrandtized"

type Equation a = (Either (Var a) (Func a), Either (Var a) (Func a))
type Sigma a = [Equation a]

unify :: Eq a => Atomic a -> Atomic a -> Sigma a -> Maybe (Sigma a)
unify (Predicate x xs) (Negated y ys) sigma
    | x /= y || length xs /= length ys = Nothing
    | null xs && null ys = Just sigma -- Just a check for speedup
    | otherwise = unify' $ (zip xs ys) ++ sigma
unify (Negated x xs) (Predicate y ys) sigma
    | x /= y || length xs /= length ys = Nothing
    | null xs && null ys = Just sigma -- Just a check for speedup
    | otherwise = unify' $ (zip xs ys) ++ sigma
unify _ _ _ = Nothing

unify' :: Eq a => Sigma a -> Maybe (Sigma a)
unify' sigma =
    let go1 [] = Just ([], [])
        go1 (pair@(Left v@(Var x), t@(Left (Var y))):rest)
            | x == y = go1 rest
            | otherwise = go2 pair =<< (go1 $ replace v t rest)
        go1 (pair@(Left v, t@(Right _)):rest)
            | occurs v t = Nothing
            | otherwise = go2 pair =<< (go1 $ replace v t rest)
        go1 ((t@(Right _), Left v):rest)
            | occurs v t = Nothing
            | otherwise = go2 (Left v, t) =<< (go1 $ replace v t rest)
        go1 (pair:rest) = go2 pair =<< go1 rest

        go2 pair (sigma, subs) = case foldl' go2' pair subs of
            p@(Left v, t) -> return (p:sigma, p:subs)
            p -> return (p:sigma, subs)

        go2' pair (Left v, t) = head $ replace v t [pair]
        go2' _ _ = error "Illegal situation" --Should never occur

    in  fst <$> go1 sigma >>= decompose


occurs :: Eq a => (Var a) -> Either (Var a) (Func a) -> Bool
occurs v (Right (Func f fs)) = any (occurs v) fs
occurs v (Left v') = v == v'

replace :: Eq a => (Var a) -> Either (Var a) (Func a) -> Sigma a -> Sigma a
replace v t sigma =
    let fstHalf = map (replace' v t . fst) sigma
        sndHalf = map (replace' v t . snd) sigma
    in  zip fstHalf sndHalf
    where
        replace' v t (Left v')
            | v == v' = t
            | otherwise = Left v'
        replace' v t (Right (Func f fs)) =
            Right (Func f $ map (replace' v t) fs)

decompose :: Eq a => Sigma a -> Maybe (Sigma a)
decompose sigma =
    case viewBy (\case (Right _, Right _) -> True; _ -> False) sigma of
        Nothing -> return sigma
        Just ((Right (Func f fs), Right (Func g gs)), rest)
            | f /= g || length fs /= length gs -> Nothing
            | otherwise -> do
                s <- unify' $ zip fs gs
                if | null s -> decompose rest
                   | null rest -> return s
                   | otherwise -> unify' (s ++ rest)

-- Extract the first occurance of anything that satisfies the pradicate, if any.
viewBy :: (a -> Bool) -> [a] -> Maybe (a, [a])
viewBy f [] = Nothing
viewBy f (x:xs)
    | f x = Just (x, xs)
    | otherwise = (fmap . fmap) (x:) $ viewBy f xs

{-
type DCFState a = State (Int, [Formula a]) (Formula a)

getNewVar :: State (Int, [Formula Int]) Int
getNewVar = do (var, _) <- modify' (\(var, set) -> (var + 1, set)) >> get
               return var

getDCFSet :: State (Int, [Formula Int]) [Formula Int]
getDCFSet = gets (\(_, set) -> set)

putDCFSet :: [Formula Int] -> State (Int, [Formula Int]) ()
putDCFSet set = modify' (\(var, _) -> (var, set))

getDefinitionalTuple :: DCFState Int -> State (Int, [Formula Int]) (Formula Int, [Formula Int])
getDefinitionalTuple = mapState (\(f, s@(_, set)) -> ((f, set), s))

--Definitional clausal form translation
--Assumes mapInts has been applied to the formula
dcfTranslation :: Formula Int -> Formula Int
dcfTranslation f = tupleToDNF . evalState (getDefinitionalTuple . dcfStateTrans $ f)
                   $ (findMax f, [])
-- The sub formulas are evaluated from right to left to preserve the original
-- ordering of the variable. This is mostly done for debugging purposes
dcfStateTrans :: Formula Int -> DCFState Int
dcfStateTrans (Atom n) = return $ Atom n
dcfStateTrans (Not (Atom n)) = return $ Not (Atom n)
dcfStateTrans ((f1 `Or` f2) `And` (f3 `Or` f4)) = do
    f4' <- dcfStateTrans f4
    f3' <- dcfStateTrans f3
    f2' <- dcfStateTrans f2
    f1' <- dcfStateTrans f1
    newVar1 <- getNewVar
    newVar2 <- getNewVar
    set <- getDCFSet
    putDCFSet $ (Not (Atom newVar2) `And` f1') : (Not (Atom newVar2) `And` f2') :
                (Not (Atom newVar1) `And` f3') : (Not (Atom newVar1) `And` f4') : set
    return (Atom newVar2 `And` Atom newVar1)

dcfStateTrans ((f1 `Or` f2) `And` f3) = do
    f3' <- dcfStateTrans f3
    f2' <- dcfStateTrans f2
    f1' <- dcfStateTrans f1
    newVar <- getNewVar
    set <- getDCFSet
    putDCFSet $ (Not (Atom newVar) `And` f1') : (Not (Atom newVar) `And` f2') : set
    return (Atom newVar `And` f3')

dcfStateTrans (f1 `And` (f2 `Or` f3)) = do
    f3' <- dcfStateTrans f3
    f2' <- dcfStateTrans f2
    newVar <- getNewVar
    set <- getDCFSet
    putDCFSet $ (Not (Atom newVar) `And` f2') : (Not (Atom newVar) `And` f3') : set
    f1' <- dcfStateTrans f1
    return (f1' `And` Atom newVar)

dcfStateTrans (f1 `And` f2) = do
    f2' <- dcfStateTrans f2
    f1' <- dcfStateTrans  f1
    return (f1' `And` f2')

dcfStateTrans (f1 `Or` f2) = do
    f2' <- dcfStateTrans f2
    f1' <- dcfStateTrans f1
    return (f1' `Or` f2')

dcfStateTrans _ = error "Formula is not in negated normal form"

--Assumes the formula is in negated normal form
tupleToDNF :: (Formula Int, [Formula Int]) -> Formula Int
tupleToDNF (formula, formulas) =
    let mappedformulas = map dnf formulas
    in  if null mappedformulas then formula
        else formula `Or` foldr1 Or mappedformulas
-}

type Clause a = Set (Atomic a)
type Path a = Set (Atomic a)
type Matrix a = [Clause a]

-- Assumes the formula is herbrandtized and in dnf.
-- This funtion will transform a formula in dnf into set of sets of atomic
-- formulas, represented as a list of sets. It will also do a bit of pruning
-- eliminating all clauses countaining p and ~p for all predicates p. If all
-- clauses are of the form mentioned above, the resulting value is [], since the
-- formula is unsatisfiable; otherwise the return value is a normal list.
connectionClauses :: Ord a => Formula a -> Matrix a
connectionClauses f = sortOn length . rmdups . evalState (finally f) $ (Just S.empty)
    where
        go :: Ord a => Formula a -> State (Maybe (Clause a)) (Matrix a -> Matrix a)
        go (Pred p xs) = do
            maybeSet <- get
            case maybeSet of
                Nothing -> return id
                Just set ->
                    if member (Negated p xs) set then put Nothing >> return id
                    else put (Just (S.insert (Predicate p xs) set)) >> return id

        go (Not (Pred p xs)) = do
            maybeSet <- get
            case maybeSet of
                Nothing -> return id
                Just set ->
                    if member (Predicate p xs) set then put Nothing >> return id
                    else put (Just (S.insert (Negated p xs) set)) >> return id

        go (f1 `And` f2) = go f2 >> go f1

        go (f1 `Or` f2) = do
            put (Just S.empty)
            sets2 <- go f2
            maybeSet2 <- get
            let set2 = maybe id (\set -> (set:)) maybeSet2

            put (Just S.empty)
            sets1 <- go f1
            maybeSet1 <- get
            let set1 = maybe id (\set -> (set:)) maybeSet1

            put Nothing
            return (set1 . sets1 . set2 . sets2)

        go _ = error "Not in disjunctive normal form"

        finally :: Ord a => Formula a -> State (Maybe (Clause a)) (Matrix a)
        finally formula = do
            sets <- go formula
            maybeSet <- get
            return $ maybe sets (\set -> (set:) . sets) maybeSet $ []

-- remove duplicate elements
-- essentially the same function as Nikita Volkov's answer on stack overflow
-- https://stackoverflow.com/questions/16108714/haskell-removing-duplicates-from-a-list
rmdups :: Ord a => [a] -> [a]
rmdups = go S.empty
    where
        go _ [] = []
        go set (x:xs) = if S.member x set then go set xs
                        else x : go (S.insert x set) xs

allM :: Monad m => (a -> m Bool) -> [a] -> m Bool
allM f = go f
    where
        go _ [] = return True
        go f (x:xs) = do
            bool <- f x
            if bool then allM f xs else return False

anyM :: Monad m => (a -> m Bool) -> [a] -> m Bool
anyM f = go f
    where
        go _ [] = return False
        go f (x:xs) = do
            bool <- f x
            if bool then return True else anyM f xs

-- will delete an element on each index, and return pairs, containing the deleted
-- element and the rest of the list
-- Example: splitViews [1,2,3] = [(1,[2,3]), (2,[1,3]), (3,[1,2])]
splitViews :: [a] -> [(a, [a])]
splitViews [] = []
splitViews (x:xs) = (x, xs) : ((fmap . fmap) (x:) $ splitViews xs)

-- Efficient way of finding all Predicates or Negated atoms with name p
members :: Ord a => Atomic a -> Clause a -> Clause a
members (Predicate p _) =
    S.takeWhileAntitone (\case Predicate p' _ -> p == p'; _ -> False)
    . S.dropWhileAntitone (\case Predicate p' _ -> p' < p; _ -> False)
members (Negated p _) =
    S.takeWhileAntitone (\case Negated p' _ -> p == p'; _ -> False)
    . S.dropWhileAntitone (\case Negated p' _ -> p' < p; _ -> True)

member :: Ord a => Atomic a -> Clause a -> Bool
member p = (/= S.empty) . members p

notMember :: Ord a => Atomic a -> Clause a -> Bool
notMember p = (== S.empty) . members p

prove :: Ord a => Matrix a -> Proof
prove formulas = if start (splitViews formulas) S.empty == True then Valid else Invalid
    where
        -- The formula is valid if it can prove the formula is valid starting
        -- from eny clause
        start :: Ord a => [(Clause a, Matrix a)] -> Path a -> Bool
        start clauseMatrixPair path = any (\(clause, matrix) ->
            snd $ solve clause path matrix []) $
            filter (positiveClause . fst) clauseMatrixPair

        positiveClause = all (\case (Predicate _ _) -> True; _ -> False)

        -- remove clauses which contains atoms that exists in the current clause
        pruneMatrix :: Ord a => Matrix a -> Clause a -> Matrix a
        pruneMatrix = foldr (\atom -> filter (notMember atom))

        -- find all clauses that clashes with p, meaning, all clauses that
        -- contain the compliment of p. Returns a list of pairs containing
        -- whith a clashing clause, and all other unvisited clauses.
        findClashingClauses :: Ord a => Atomic a -> Matrix a -> [(Clause a, Matrix a)]
        findClashingClauses (Predicate p xs) = filter (\(set, _) ->
            member (Negated p xs) set) . splitViews
        findClashingClauses (Negated p xs) = filter (\(set, _) ->
            member (Predicate p xs) set) . splitViews

        solve :: Ord a => Clause a -> Path a -> Matrix a -> Sigma a -> (Sigma a, Bool)
        solve clause path matrix sigma =
            let newMatrix = pruneMatrix matrix clause
            in  undefined -- all (\atom -> closeBranch atom path newMatrix) clause

        -- If the compliment of p exists in the path, then we can close that branch
        reductionRule (Predicate p xs) = member (Negated p xs)
        reductionRule (Negated p xs) = member (Predicate p xs)

        -- Returns true if it can close any branch starting starting from atom
        findPath atom path sigma =
            let newPath = (S.insert atom path)
            in  undefined -- any (\(clause, matrix) ->
                -- solve clause newPath matrix) . findClashingClauses atom

        -- A branch can be closed if it can apply the reduction rule, or find
        -- a path that closes the formula
        closeBranch :: Ord a => Atomic a -> Path a -> Matrix a -> Sigma a -> (Sigma a, Bool)
        closeBranch atom path matrix sigma = undefined -- reductionRule atom path || findPath atom path matrix
