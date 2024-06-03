# A Formal Semantics of Solidity in Isabelle/HOL

This directory contains a formal semantics of Solidity in Isabelle/HOL. 
Initially, this semantics has been developed in Haskell and translated
in an "ad-hoc" way using an "in-house" version of Haskabelle for 
Isabelle 2017 and, thereafter, the generated theories have been ported
to Isabelle 2021-1. The formalization is stored in the directory 
[Solidity](./Solidity).

## Prerequisites

* The formalization requires [Isabelle 2021-1](https://isabelle.in.tum.de/). 
  Please follow the instructions on the Isabelle home page for your operating 
  system. In the following, we assume that the ``isabelle`` tool is available
  on the command line. This might require to add the Isabelle binary directory
  to the ``PATH`` environment variable of your system. 

* The Solidity evaluator used for testing the formalization against the 
  real Solidity system requires [The Haskell Tool Stack](https://docs.haskellstack.org/en/stable/README/). 
  The Haskell Tool Stack can either be installed as a stand-alone tool
  or as integrated tool within Isabelle. For the latter, one only 
  needs to execute:

  ```sh
  isabelle ghc_setup
  ```

## Using the Formalization

The formalization can be loaded into Isabelle/jEdit by executing 

```sh
isabelle jedit Solidity_Main.thy
```

on the command line. Alternatively, you can start Isabelle/jEdit by 
clicking on the Isabelle icon and loading the theory 
[Solidity_Main.thy](./Solidity_Main.thy) manually. 

To use a command line build that also generates a PDF document,
first add ``path/to/solidity`` to your Isabelle roots file which is
a file called ``ROOTS`` in your Isabelle home directory.
Then, the build can be started by executing:

```sh
isabelle build -D .
```

To export the generated Haskell sources, use the ``-e`` option during 
the build, e.g.:

```sh
isabelle build -e -D .
```

The sources of the Solidity evaluator are exported into the directory 
[Solidity/solidity-evaluator](./solidity-evaluator). The sources
can be compiled using the Haskell Stack, either in its stand-alone version or using 
the version integrated into Isabelle. For the former use:

```
stack build --coverage 
stack run solidity-evaluator
```

For the Haskell Stack integrated into Isabelle use (you might need to run 
``isabelle ghc_setup`` first):

```
isabelle ghc_stack build --coverage 
isabelle ghc_stack run solidity-evaluator
```

## Code Coverage

### General (from <https://docs.haskellstack.org/en/stable/coverage/>)

To obtain coverage info do following 
1. Build with `stack build --coverage`
2. Executing solidity-exe generates a file `solidity-exe.tix`
3. Copy `solidity-exe.tix` to solidity home and execute `stack hpc report solidity-exe.tix`
4. HTML reports are available at `$(stack path --local-hpc-root)`

### Include specific modules
To create a coverage report which includes only specific modules use `stack exec hpc -- markup solidity-evaluator.tix --hpcdir=.stack-work/dist/x86_64-linux-tinfo6/Cabal-2.4.0.1/hpc --srcdir=. --include=Accounts Declarations Environment Expressions Statements Storage Store Utils Valuetypes`

### Exclude testing code (from <http://wiki.haskell.org/Haskell_program_coverage>)
To exclude testing related code do the following:
1. Create complete coverage file with `stack exec hpc -- draft --hpcdir=.stack-work/dist/x86_64-linux-tinfo6/Cabal-2.4.0.1/hpc --srcdir=. solidity-evaluator.tix > draft.txt`
2. Modify draft.txt to check all the commands which should not be considered in the coverage. In particular replace `:` with `/` in `solidity-evaluator-0.1.0.0-E6rYduruX84J8q3ItmGdtm:Solidity`
3. Create tix file with `stack exec hpc -- overlay --hpcdir=.stack-work/dist/x86_64-linux-tinfo6/Cabal-2.4.0.1/hpc --srcdir=. draft.txt > draft.tix`
4. Create combined tix file with `stack exec hpc -- combine solidity-evaluator.tix draft.tix --union > combined.tix`
5. Execute `stack hpc report combined.tix`
