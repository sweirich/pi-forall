pi-forall
=========

A demo implementation of a simple dependently-typed language for OPLSS
(Used in 2022, 2014 and 2013)

The goal of this project is to bring up the design issues that occur in the
implementation of the type checkers of languages like Agda, Coq, Epigram, Idris, etc. Of course, it
can't cover everything, but this code is a starting point for discussion.

As its main purpose is didactic, the code itself has been written for
clarity, not for speed. The point of this implementation is an introduction to
practical issues of language design and how specific features interact with
each other. 

Installation
----------
  pi-forall requires GHC and cabal or stack
  
  Recommended tools:
  
  1. gchup: See instructions here [https://www.haskell.org/ghcup/]
  
  The gchup tool is an installer for general purpose Haskell tools, including GHC, cabal, stack and the Haskell language server (HLS). You'll want to have the recommended versions of all of these tools installed. 

  2. VSCode and Haskell language extension   

  Installation instructions for VS Code are [here](https://code.visualstudio.com/). This should be used with the [Haskell VSCode extension](https://marketplace.visualstudio.com/items?itemName=haskell.haskell).

Contents
--------

There are several versions of `pi-forall` in the repository. See the 
[documentation](https://github.com/sweirich/pi-forall/blob/2022/doc/oplss.pdf) for an extended description of what parts of the language
are covered by each version. 

Each implementation has the following structure:

```
<version>/
  pi/*.pi            example pi-forall files
  src/*.hs           source code
  app/Main.hs        entry point
  README.md (this file)
  LICENSE
  pi-forall.cabal
  stack.yaml         

```

Acknowledgement
---------------

Some of this code was adapted from the 'zombie-trellys' implementation by the
Trellys team. The Trellys team includes Aaron Stump, Tim Sheard, Stephanie
Weirich, Garrin Kimmell, Harley D. Eades III, Peng Fu, Chris Casinghino,
Vilhelm Sjöberg, Nathan Collins, and Ki Yung Ahn.

This material is based upon work supported by the National Science Foundation
under Grant Number 0910786. Any opinions, findings, and conclusions or
recommendations expressed in this material are those of the author(s) and do
not necessarily reflect the views of the National Science Foundation.
