HTML_FILES = stack_machine.html induction.html
PDF_FILES = cpdt.pdf
TEX_CHAPTERS = stack_machine.tex induction.tex

%.html: %.glob
	coqdoc $*.v

cpdt.pdf: CpdtTactics.glob cpdt.tex $(TEX_CHAPTERS)
	xelatex cpdt.tex
	xelatex cpdt.tex

%.tex: %.glob
	coqdoc -latex --body-only -s $*.v

%.glob: %.v
	coqc $<


all: CpdtTactics.glob $(HTML_FILES) $(PDF_FILES)

clean:
	rm -f *.glob *.vo $(TEX_CHAPTERS) *.log *.aux *.sty

nuke: clean
	rm -f *.pdf *.html *.css
