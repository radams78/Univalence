agdatex := $(subst src/,latex/,$(subst .lagda,.tex,$(shell find src -name *.lagda)))

all: main.article.pdf main.beamer.pdf
latex/%.tex: src/%.lagda
	@cd src; agda -i . -i ${AGDALIBDIR} --latex --latex-dir=../latex $*.lagda
main.%.pdf: $(agdatex) latex/main.%.tex latex/main.tex
	@cd latex;latexmk -g -pdf main.$*
