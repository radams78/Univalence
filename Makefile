all: Grammar.agdai Reduction.agdai Prelims.agdai PL.agdai PHOPL.agdai
%.agdai: %.lagda
	agda $< 
abstract.pdf: abstract.tex
	latexmk -pdf -g abstract
