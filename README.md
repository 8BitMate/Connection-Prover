# Connection Prover

This is a prover for propositional formulas using the connection method.

## Install

In order to compile and run this program you need to install [stack](https://docs.haskellstack.org/en/stable/install_and_upgrade/).
After installing stack, move into the project folder and type: 'stack build' to
compile the project and install necessary dependencies.

## Run

After compiling, run the program by typing stack exec prover-exe [args]. To run
tests, type stack test. The args for prover-exe is an optional parameter that is
either dnf or dcf, followed by a path to a file with the proof you want to check.

## File format

The file format is: fof(\<name\>, conjecture, \<formula\>). Where \<name\> is
the name of the formula, and formula is the formula you want to check.

propositional variables are strings consisting of any letters or numbers, or the
character '_'  And expressions are on the form: f1 & f2, or expressions are on
the form f1 | f2, implication is on the form f1 -> f2 and not expressions is on
the form ~ f. Normal precedence rules should hold, but this is not thoroughly
tested.
