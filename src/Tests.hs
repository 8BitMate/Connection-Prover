module Tests where

import Prover

testFormula1 = Not (Not (Atom 'a' `And` Atom 'b' `And` Atom 'c') `And` Not (Not (Atom 'a' `And` Not (Not (Atom 'a' `And` Atom 'c')))))-- ~ (~ (a & b & c) & ~ ~ (a & ~ ~ (b & c)))
testFormula2 = (Atom 'a' `And` ((Atom 'b' `And` (Atom 'c' `And` Atom 'd')) `And` (Atom 'e' `And` (Atom 'f' `And` Atom 'g'))))
testFormula3 = (Atom 'a' `And` Atom 'b' `And` Atom 'c') `Or` (Not (Atom 'a') `Or` (Not (Atom 'a') `Or` (Not (Atom 'c'))))
testCNF1 = (((Atom 'a' `And` (Atom 'b' `Or` Atom 'c')) `And` (Atom 'a' `Or` (Atom 'p' `And` Atom 'q'))) `And` (Atom 'p' `Or` Atom 'r'))
testCNF2 = (((Atom 'a' `And` (Atom 'b' `Or` Atom 'c')) `And` ((Atom 'p' `And` Atom 'q') `Or` Atom 'a')) `And` (Atom 'p' `Or` Atom 'r'))
testCNF3 = (((Atom 'a' `And` (Atom 'b' `Or` Atom 'c')) `And` (Atom 'p' `Or` (Atom 'q' `Or` Atom 'a'))) `And` (Atom 'p' `Or` Atom 'r'))
testDCFTrans1 = (Atom 'p' `Or` Atom 'q') `And` (Atom 'q' `Or` Atom 'r') `And` (Atom 'r' `Or` Atom 's')
testDCFTrans2 = (Atom 'p' `Or` Atom 'q') `And` ((Atom 'q' `Or` Atom 'r') `And` (Atom 'r' `Or` Atom 's'))
testDCFTrans3 = (Atom 'p' `Or` Atom 'q') `And` ((Atom 'q' `Or` Atom 'r' `Or` Atom 's') `And` (Atom 'r' `Or` Atom 's'))
testDCFTrans4 = (Atom 'p' `Or` Atom 'q') `And` (Atom 'q' `Or` ((Atom 'r' `Or` Atom 's') `And` Atom 'd'))

--This function will group a formula in negated normal form and rearange the
--subformulas in a way that makes them easier to reason with later.
--I may not need this after all
organizeParens :: Formula a -> Formula a
organizeParens (Atom p) = Atom p
organizeParens (Not (Atom p)) = Not (Atom p)
organizeParens (f1 `And` (f2 `And` f3)) = organizeParens ((f1 `And` f3) `And` f3)
organizeParens (f1 `And` f2) = organizeParens f1 `And` organizeParens f2
organizeParens (f1 `Or` (f2 `Or` f3)) = organizeParens ((f1 `Or` f3) `Or` f3)
organizeParens (f1 `Or` f2) = organizeParens f1 `Or` organizeParens f2
organizeParens _ = error "Formula is not in negated normal form"


isCNF :: Formula a -> Bool
isCNF (Atom _) = True
isCNF (Not (Atom _)) = True
isCNF (f1 `Or` (f2 `And` f3)) = False
isCNF ((f1 `And` f2) `Or` f3) = False
isCNF (f1 `And` f2) = isCNF f1 && isCNF f2
isCNF (f1 `Or` f2) = isCNF f1 && isCNF f2
isCNF _ = error "Formula is not in negated normal form"

isDNF :: Formula a -> Bool
isDNF (Atom _) = True
isDNF (Not (Atom _)) = True
isDNF (f1 `And` (f2 `Or` f3)) = False
isDNF ((f1 `Or` f2) `And` f3) = False
isDNF (f1 `And` f2) = isDNF f1 && isDNF f2
isDNF (f1 `Or` f2) = isDNF f1 && isDNF f2
isDNF _ = error "Formula is not in negated normal form"
