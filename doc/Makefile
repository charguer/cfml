TARGET = compil_clight

all: $(TARGET).pdf

.PHONY: FORCE entr

%.pdf: %.tex FORCE
	latexrun --latex-cmd 'xelatex' $<

entr: $(TARGET).tex
	ls $< | entr -s 'make'
