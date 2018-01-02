# Connection Prover

This is a prover for propositional formulas using the connection method.

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
stack exec prover-exe [args]
```
To run tests, type
```
stack test
```
The args for prover-exe is an optional parameter
that is either dnf or dcf, followed by a path to a file with the proof you want
to check.

dnf stands for disjunctive normal form, and is the standard normal form
translation. dcf stands for definitional clausal form, which is a different
kind of translation to clausal form. Different kinds of translations might be
suited for different problems, so I have included both. If no arguments are
given the dnf translation is chosen by default.

## File format

The file format is: fof(\<name\>, conjecture, \<formula\>). Where \<name\> is
the name of the formula, and formula is the formula you want to check.

propositional variables are strings consisting of any letters or numbers, or the
character '_'  And expressions are on the form: f1 & f2, or expressions are on
the form f1 | f2, implication is on the form f1 -> f2 and not expressions is on
the form ~ f. Normal precedence rules should hold, but this is not thoroughly
tested.
