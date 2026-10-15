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
+ [let.ott](let.ott) - Let expressions and definitions
+ [template.ott](template.ott) - Empty template for adding a new language feature (not used by the Makefile)

These files are not processed separately: the Makefile passes `pi.ott`,
`sigma.ott`, `bool.ott`, `tyeq.ott`, `epsilon.ott`, `data.ott` and `let.ott`
to Ott together (with `-merge true`), so grammar productions and rules with
the same judgment names are combined into a single specification. The
generated macros are written to `pi-rules.tex` and used to typeset
`oplss.mng`.

LaTeX source files
+ [oplss.mng](oplss.mng) - Main text of the document
+ [lstpi.sty](lstpi.sty) - [Listings](https://ctan.mirrors.hoobly.com/macros/latex/contrib/listings/listings.pdf) specification for  typesetting `pi-forall` source code
+ [lstparams.sty](lstparams.sty), [lsthaskell.sty](lsthaskell.sty), [listproc.sty](listproc.sty) - supporting style files for code listings (including Haskell)
+ [ottalt.sty](ottalt.sty) - [Auxiliary style file](https://users.cs.northwestern.edu/~jesse/code/latex/ottalt/ottalt.pdf) for working with Ott produced LaTeX macros
+ [weirich.bib](weirich.bib) - BibTeX data
+ Makefile - how to put everything together
