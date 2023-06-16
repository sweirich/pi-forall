pi-forall language
------------------

This language implementation is designed to accompany four lectures at
OPLSS during Summer 2023. Notes for these lectures are included in the
distribution:

- [oplss.pdf](doc/oplss.pdf)

(The documentation [README.md](doc/README.md) includes details about
how the notes are typeset.)

These lecture notes correspond to an increasingly expressive demo
implementation of a dependently-typed lambda calculus. Each of the
following subdirectories is a self-contained implementation, and all 
are generated from the same source, located in the [main/](main/) 
directory. 

- [version1/](version1/):   Basic language implementation
- [version2/](version2/):   Basic language extended with nontrivial definitional equality
- [version3/](version3/):   Above, extended with irrelevant arguments
- [full/](full/):           Full language with datatypes

The implementation [README.md](main/README.md) includes instructions about
how to compile and work with these implementations. Edits should only be for 
versions in the [main/](main/) directory.

History
-------

This is a revised version of lecture notes originally presented at OPLSS
during 2022, 2014 and 2013.

Videos from the 2014 lectures are also available from the
[OPLSS website](https://www.cs.uoregon.edu/research/summerschool/summer14/curriculum.html).
If you want to watch these videos, you should look at the
2014 branch of this repository.

An abridged version of these lectures was also given at the Compose
Conference, January 2015. Notes from this version are also available.

- [compose.md](old/compose.md): Overview of pi-forall implementation

--
Stephanie Weirich
