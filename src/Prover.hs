{-# LANGUAGE LambdaCase, DeriveFunctor #-}

module Prover where

import Prelude hiding (lookup)
import Data.Map (Map (..))
import qualified Data.Map as M
import Data.Set (Set (..))
import qualified Data.Set as S
import Data.List (sortOn, intercalate)
import Control.Monad.State.Strict
import Data.Foldable
-- |
-- This is a connection logic prover for first order logic

-- I treat a funtion with no variables as a constant, and a predicate with no
-- variables as an atomic formula
newtype Var a = Var a deriving (Eq, Ord, Functor)
data Func a = Func a [Either (Var a) (Func a)] deriving Eq

data Formula a = Pred a [Either (Var a) (Func a)]
             | Not (Formula a)
             | Formula a `And` Formula a
             | Formula a `Or` Formula a
             | Formula a `Implies` Formula a
             | Forall (Var a) (Formula a)
             | Exists (Var a) (Formula a) deriving Eq

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
    show (Func f ls) = show f ++ show "(" ++ intercalate ", "
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

test = "![X]: (p(X) & b & (![X]: q(X)) & q(X))"

-- Converts the predicates, functions on variables to int values.
-- All variables bound to a quantifier is given a unique number, even if the
-- same variable is used elsewhere. For example:
-- ![X]: ?[Y]: p(X,Y) & ?[Y] p(Y,X) will be converted to:
-- ![0]: ?[1]: p(0,1) & ?[2] p(2,0)
mapInts :: Ord a => Formula a -> Formula Int
mapInts f = evalState (go M.empty f) (0, M.empty, M.empty)
    where
        go :: Ord a => Map (Var a) Int -> Formula a -> State (Int, Map a Int, Map a Int) (Formula Int)
        go vars (Pred p xs) = do
           (varNum, preds, funcs) <- get
           case M.lookup p preds of
                Nothing -> do put (varNum + 1, M.insert p varNum preds, funcs)
                              xs' <- mapM (replaceVarOrFunc vars) xs
                              return $ Pred varNum xs'
                Just n -> do xs' <- mapM (replaceVarOrFunc vars) xs
                             return $ Pred n xs'
        go vars (Not f1) = do f1' <- go vars f1; return $ Not f1'
        go vars (f1 `And` f2) = do
            f1' <- go vars f1
            f2' <- go vars f2
            return (f1' `And` f2')
        go vars (f1 `Or` f2) = do
            f1' <- go vars f1
            f2' <- go vars f2
            return (f1' `Or` f2')
        go vars (f1 `Implies` f2) = do
            f1' <- go vars f1
            f2' <- go vars f2
            return (f1' `Implies` f2')
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
                                  -> State (Int, Map a Int, Map a Int) (Either (Var Int) (Func Int))
        replaceVarOrFunc vars (Left var) = return $ case M.lookup var vars of
            Nothing -> error "Formula contains free variables"
            Just n -> Left (Var n)
        replaceVarOrFunc vars (Right (Func name xs)) = do
            (varNum, preds, funcs) <- get
            case M.lookup name preds of
                Nothing -> do
                    put (varNum + 1, preds, M.insert name varNum funcs)
                    xs' <- mapM (replaceVarOrFunc vars) xs
                    return $ Right (Func varNum xs')
                Just n -> do
                    xs' <- mapM (replaceVarOrFunc vars) xs
                    return $ Right (Func n xs')

        newVarNum :: Ord a => State (Int, Map a Int, Map a Int) Int
        newVarNum = do
            (varNum, preds, funcs) <- get
            put (varNum + 1, preds, funcs)
            return varNum
{-
findMaxInt :: Formula Int -> Int
findMaxInt (Atom n) = n
findMaxInt (Not (Atom n)) = n
findMaxInt (f1 `And` f2) = max (findMaxInt f1) (findMaxInt f2)
findMaxInt (f1 `Or` f2) = max (findMaxInt f1) (findMaxInt f2)
findMaxInt _ = error "Formula is not in negated normal form"

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
                   $ (findMaxInt f, [])
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

--Assumes the formula is in negated normal form
--This is the standard translation into disjunctive normal form
dnf :: Show a => Formula a -> Formula a
dnf (Atom p) = Atom p
dnf (Not (Atom p)) = Not (Atom p)
dnf ((f1 `Or` f2) `And` f3) = dnf (f1 `And` f3) `Or` dnf (f2 `And` f3)
dnf (f1 `And` (f2 `Or` f3)) = dnf (f1 `And` f2) `Or` dnf (f1 `And` f3)
dnf (f1 `And` f2) =
    let f1' = dnf f1
        f2' = dnf f2
        isOr (_ `Or` _) = True
        isOr _ = False
    in  if isOr f1' || isOr f2' then dnf (f1' `And` f2') else f1' `And` f2'
dnf (f1 `Or` f2) = dnf f1 `Or` dnf f2


-- Assumes the Formula is in dnf
-- This funtion will transform a formula in dnf into set of sets of atomic
-- formulas, represented as a list of sets. It will also do a bit of pruning
-- eliminating all clauses countaining p and ~p for all predicates p. If all
-- clauses are of the form mentioned above, the resulting value is [], since the
-- formula is unsatisfiable; otherwise the return value is a normal list.
connectionClauses :: Ord a => Formula a -> [Set (Atomic a)]
connectionClauses f = sortOn length . rmdups . evalState (finally f) $ (Just S.empty)
    where
        go :: Ord a => Formula a -> State (Maybe (Set (Atomic a))) ([Set (Atomic a)] -> [Set (Atomic a)])
        go (Atom p) = do
            maybeSet <- get
            case maybeSet of
                Nothing -> return id
                Just set ->
                    if S.member (Negated p) set then put Nothing >> return id
                    else modify' (fmap (S.insert (Atomic p))) >> return id

        go (Not (Atom p)) = do
            maybeSet <- get
            case maybeSet of
                Nothing -> return id
                Just set ->
                    if S.member (Atomic p) set then put Nothing >> return id
                    else modify' (fmap (S.insert (Negated p))) >> return id

        go (f1 `And` f2) = do
            go f2 >> go f1

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

        finally :: Ord a => Formula a -> State (Maybe (Set (Atomic a))) [Set (Atomic a)]
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

-- will delete an element on each index, and return pairs, containing the deleted
-- element and the rest of the list
-- Example: splitViews [1,2,3] = [(1,[2,3]), (2,[1,3]), (3,[1,2])]
splitViews :: [a] -> [(a, [a])]
splitViews [] = []
splitViews (x:xs) =
    let views = splitViews xs
        views' = map (\(y, ys) -> (y, x:ys)) views
    in  (x, xs) : views'

-- I made these two functions for future optimizations
-- I tried to do this method using different kinds of folds, but I could not
-- ensure lazyness, so I gave up and did it with normal recursion
allM :: (Foldable t, Monad m) => (a -> m Bool) -> t a -> m Bool
allM f = go f . toList
    where
        go _ [] = return True
        go f (x:xs) = do
            bool <- f x
            if bool then allM f xs else return False

anyM :: (Foldable t, Monad m) => (a -> m Bool) -> t a -> m Bool
anyM f = go f . toList
    where
        go _ [] = return False
        go f (x:xs) = do
            bool <- f x
            if bool then return True else anyM f xs

prove :: Ord a => [Set (Atomic' a)] -> Proof
prove formulas = if start (splitViews formulas) S.empty == True then Valid else Invalid
    where
        -- The formula is valid if it can prove the formula is valid starting
        -- from eny clause
        start :: Ord a => [(Set (Atomic' a), [Set (Atomic' a)])] -> Set (Atomic' a) -> Bool
        start formulaMatrixPair path = any (\(clause, matrix) ->
            solve clause path matrix) $ formulaMatrixPair

        solve clause path matrix =
            let newMatrix = pruneMatrix matrix path
            in  all (\atom -> closeBranch atom path newMatrix) clause

        -- If the compliment of p exists in the path, then we can close that branch
        reductionRule (Atomic' p) = S.member (Negated p)
        reductionRule (Negated p) = S.member (Atomic' p)

        -- remove clauses which contains atoms that exists in the current clause
        pruneMatrix :: Ord a => [Set (Atomic' a)] -> Set (Atomic' a) -> [Set (Atomic' a)]
        pruneMatrix = foldr (\atom -> filter (S.notMember atom))

        -- find all clauses that clashes with p, meaning, all clauses that
        -- contain the compliment of p. Returns a list of pairs containing
        -- whith a clashing clause, and all other unvisited clauses.
        findClashingClauses (Atomic' p) = filter (\(set, _) ->
            S.member (Negated p) set) . splitViews
        findClashingClauses (Negated p) = filter (\(set, _) ->
            S.member (Atomic' p) set) . splitViews

        -- Returns true if it can close any branch starting starting from atom
        findPath atom path =
            let newPath = (S.insert atom path)
            in  any (\(clause, matrix) ->
                solve clause newPath matrix) . findClashingClauses atom

        -- A branch can be closed if it can apply the reduction rule, or find
        -- a path that closes the formula
        closeBranch atom path matrix = reductionRule atom path || findPath atom path matrix
-}
