all:
	pdflatex linklets.tex
	bibtex linklets.aux
	pdflatex linklets.tex

sample:
	pdflatex sample.tex

remove-pdf:
	$(RM) linklets.pdf

clean: remove-pdf
	$(RM) *.log *.aux *~ \
	*.cfg *.glo *.idx *.toc \
	*.ilg *.ind *.out *.lof \
	*.lot *.bbl *.blg *.gls *.cut *.hd \
	*.dvi *.ps *.thm *.tgz *.zip *.rpi
