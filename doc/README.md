Source files for Lecture Notes, PDF [oplss.pdf](oplss.pdf)
-----------------------------------------------------------

To typeset these notes, you will need to have installed LaTeX and the Ott tool. The easiest way to install Ott is through [opam](https://opam.ocaml.org/).

The Ott tool assists with typesetting mathematical specifications of type systems. All typing rules that appear in the lecture notes are specified within the following source files. 

[Ott](https://www.cl.cam.ac.uk/~pes20/ott/top2.html) specifications:
+ [pi.ott](pi.ott) - Core system
+ [bool.ott](bool.ott) - Booleans
+ [sigma.ott](sigma.ott) - Sigma types
+ [tyeq.ott](tyeq.ott) - Propositional equality
+ [epsilon.ott](epsilon.ott) - Irrelevance
+ [data.ott](data.ott) - Data types

LaTeX source files
+ [oplss.mng](oplss.mng) - Main text of the document
+ [lstpi.sty](lstpi.sty) - [Listings](https://ctan.mirrors.hoobly.com/macros/latex/contrib/listings/listings.pdf) specification for  typesetting `pi-forall` source code
+ [ottalt.sty](ottalt.sty) - [Auxiliary style file](https://users.cs.northwestern.edu/~jesse/code/latex/ottalt/ottalt.pdf) for working with Ott produced LaTeX macros
+ [weirich.bib](weirich.bib) - BibTeX data
+ Makefile - how to put everything together
