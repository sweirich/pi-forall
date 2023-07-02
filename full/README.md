pi-forall
=========

A demo implementation of a simple dependently-typed language for OPLSS
(Used in 2023, 2022, 2014 and 2013)

The goal of this project is to bring up the design issues that occur in the
implementation of the type checkers of languages like Agda, Coq, Epigram, 
Idris, etc. Of course, it can't cover everything, but this code is a 
starting point for discussion.

As its main purpose is didactic, the code itself has been written for
clarity, not for speed. The point of this implementation is an introduction to
practical issues of language design and how specific features interact with
each other. 

Installation
----------

  Compiling pi-forall requires GHC and stack
  
  Recommended tools (see links for instructions):
  
  1. [ghcup](https://www.haskell.org/ghcup/)
  
  The ghcup tool is an installer for general purpose Haskell tools, including GHC, Cabal, Stack and the Haskell language server (HLS). You'll want to install the recommended versions of all of these tools. Older versions are likely to work too, but the stack.yaml file will force a specific version of GHC. 

  2. [VSCode](https://code.visualstudio.com/) and [Haskell language extension](https://marketplace.visualstudio.com/items?itemName=haskell.haskell)

  I recommend using VSCode to browse and edit Haskell projects. When working with the `pi-forall` repository, you should open the folder for the specific implementation that you want to work with (i.e. `version1`/`version2`/`full`), so that the Haskell language server
can find the project metadata. If you open the toplevel `pi-forall` folder instead, you will get errors from vscode.


Project Contents
-----------------

There are several versions of `pi-forall` in the repository. See the 
[documentation](https://github.com/sweirich/pi-forall/blob/2023/doc/oplss.pdf) for an extended 
description of what parts of the language are covered by each version. 

Each implementation has the following structure:

```
<version>/
  pi/*.pi                example pi-forall files and exercises
  src/*.hs               source code
  app/Main.hs            entry point for command line app
  README.md              this file
  LICENSE                license file
  pi-forall.cabal        project metadata
  stack.yaml             project metadata

```

To build each version, use a terminal to go to that directory and type:

```
stack build
```

and to typecheck a source file:

```
stack exec -- pi-forall <sourcefile>
```


Versioning
----------

This repository has been tested with the current ghcup recommended tool versions for July 2023, including GHC 9.4.5, hsl 2.0.0.1 and stack lts-21.1.

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
