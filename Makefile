order_file := order.txt
modules := $(shell cat ${order_file})

all: $(addsuffix .agdai,$(modules)) main.beamer.pdf main.article.pdf
%.agdai: %.lagda
	agda -i . -i ${AGDALIBDIR} $< 
main.beamer.pdf: main.beamer.tex $(addsuffix .lagda,$(modules)) main.tex
	latexmk -pdf -g $<
