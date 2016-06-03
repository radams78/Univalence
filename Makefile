order_file := order.txt
modules := $(shell cat ${order_file})

all: $(addsuffix .agdai,$(modules)) main.article.pdf
%.agdai: %.lagda
	agda -i . -i ${AGDALIBDIR} $< 
main.article.pdf: main.article.tex $(addsuffix .agdai,$(modules)) main.tex
	latexmk -pdf -g $<
