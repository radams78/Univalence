agdatex := $(subst src/,latex/,$(subst .lagda,.tex,$(shell find src -name *.lagda)))

latex/%.tex: src/%.lagda
	@cd src; agda -i . -i ${AGDALIBDIR} --latex --latex-dir=../latex $*.lagda
main.article.pdf: $(agdatex) latex/main.article.tex latex/main.tex
	@cd latex;latexmk -g -pdf main.article
