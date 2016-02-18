all: Grammar.agdai Reduction.agdai Prelims.agdai PL.agdai PHOPL.agdai
%.agdai: %.lagda
	agda $< 
%.pdf: %.tex
	latexmk -pdf -g $<
