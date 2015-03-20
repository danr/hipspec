Presentation.pdf : Presentation.tex
	pdflatex Presentation.tex && ( grep -s "Rerun to get" Presentation.log && pdflatex Presentation.tex || true )

Presentation.tex : Presentation.lhs
	lhs2TeX Presentation.lhs > Presentation.tex

Presentation.aux : Presentation.tex
	pdflatex Presentation.tex

Presentation.bbl : Presentation.aux Presentation.bib
	bibtex Presentation
