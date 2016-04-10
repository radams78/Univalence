all: Grammar.agdai Reduction.agdai Prelims.agdai PL.agdai PHOPL.agdai main.pdf
%.agdai: %.lagda
	agda -i . -i /usr/share/agda-stdlib $< 
main.pdf: main.lagda
	latexmk -pdf -g $<
