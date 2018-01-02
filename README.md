# Connection Prover

This is a prover for first order formulas using the connection method. There
is an option to use exhaustive search if a proof is not found using the
non-exhaustive search. This will always find a proof if the formula is valid,
but it might not terminate at all if the formula is invalid. The most likely
reason for the program not to terminate though, is that even if a proof can
theoretically be found, it may take too much time for any person to be
patient enough to wait for it to finish.

I have a version of this prover, that only works for propositional formulas in
another git branch, which should be slightly faster for propositional formulas
and easier to understand, if anyone is interested.

## Install

In order to compile and run this program you need to install [stack](https://docs.haskellstack.org/en/stable/install_and_upgrade/).
After installing stack, move into the project folder and run the command:
```
stack build
```
to compile the project and install necessary dependencies.

## Run

After compiling, run the program by typing
```
stack exec prover-exe [e|exhaustive] <file path>
```
To run tests, type
```
stack test
```

## File format

The file format is: fof(\<name\>, conjecture, \<formula\>). Where \<name\> is
the name of the formula, and formula is the formula you want to check.

propositional variables are strings consisting of any letters or numbers, or the
character '_'  And expressions are on the form: f1 & f2, or expressions are on
the form f1 | f2, implication is on the form f1 -> f2 and not expressions is on
the form ~ f. for all X: f is written: ![X]: f,  and exists X: f is written:
?[X]: f. Normal precedence rules should hold, but this is not thoroughly tested.
