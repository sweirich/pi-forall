## Makefile for paper

OTT_SOURCE = pi sigma bool tyeq epsilon data let
BIBFILES = weirich.bib

OTTFILES  = $(foreach i, $(OTT_SOURCE), $(i).ott)
OTTIFLAGS = $(foreach i, $(OTT_SOURCE), -i $(i).ott) -merge true
RULESFILE = pi-rules.tex

PAPER_MNG = $(wildcard *.mng)
PAPER_SOURCE = $(patsubst %.mng,%.tex,$(PAPER_MNG))
OTT_FILTER := $(subst .mng,.mng ,$(addprefix -tex_filter ,$(join $(PAPER_MNG), $(PAPER_SOURCE))))

TOP=oplss
PDFS=oplss.pdf

all: $(TOP).pdf

$(TOP).tex: $(RULESFILE) $(TOP).mng Makefile
	ott $(OTTIFLAGS) \
            -tex_wrap false \
            -tex_show_meta false \
            -tex_filter $*.mng $*.tex

%.tex : $(RULESFILE) %.mng Makefile
	rm -f $(PAPER_SOURCE)
	ott -tex_wrap false \
            -tex_show_meta false \
            $(OTTIFLAGS) \
            $(OTT_FILTER)
	chmod a-w $(PAPER_SOURCE)

$(RULESFILE): $(OTTFILES)
	ott $(OTTIFLAGS) -o $(RULESFILE) \
          -tex_wrap false \
          -tex_show_meta false

$(TOP).pdf : $(TOP).tex  $(BIBFILES) $(PAPER_SOURCE) Makefile lstparams.sty lstpi.sty
	echo $(PAPER_SOURCE)
	latexmk -pdflatex="texfot pdflatex" -bibtex -pdf $(TOP).tex && latexmk -c

deps:
	echo $(PAPER_SOURCE)

paperclean:
	rm -if *-rules.tex $(TOP).tex *.log ./*~  *.aux $(PDFS) *.bbl *.blg *.fdb_latexmk *.fls *.out *-input.tex *~


clean: paperclean
