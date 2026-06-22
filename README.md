# Introduction to Rocq

A short introduction to Rocq.

## Installation Instructions

The Rocq website contains [instructions](https://rocq-prover.org/install) on how
to install all the required packages to follow this introduction. We recommend
that you install the Rocq Platform for Rocq v9.0. The website also contains
instructions on how to set up popular text editors to develop Rocq code
interactively.

## Structure

- `handouts/` contains all the source files without the solutions.
- `src/` contains the original Rocq sources, including solutions.
- `preprocess.sh` shell script to generate handouts.

## Lectures

`logic.v` is a cheat sheet with many examples of logical connectives and related
tactics.  The main lectures correspond to the following files:

- `basics.v`: Basic Rocq syntax and tactics 
- `sorting.v` Programming with lists
- `imp.v` Imperative programs
- `opt.v` Verifying a program optimizer

## Further resources

This introduction is necessarily incomplete: there are many concepts and
features of Rocq that are not covered. If you want to learn more, the Rocq
website has [several recommended books](https://rocq-prover.org/docs) targeting
beginner, intermediate and advanced readers.  The [Software Foundatations
series](https://softwarefoundations.cis.upenn.edu/), in particular, has several
books covering topics such as logical foundations, programming language theory,
separation logic, and many more.
