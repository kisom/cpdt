HTML_FILES = stack_machine.html induction.html
PDF_FILES = stack_machine.pdf induction.pdf

%.html: %.v
	coqdoc $<

%.pdf: %.tex
	xelatex $<

%.tex: %.glob
	coqdoc -latex $*.v

%.glob: %.v
	coqc $<


all: $(HTML_FILES) $(PDF_FILES)

clean:
	rm -f *.glob *.vo *.tex *.log *.aux *.sty

nuke: clean
	rm -f *.pdf *.html *.css
