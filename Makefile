order_file := order.txt
modules := $(shell cat ${order_file})

all: $(addsuffix .agdai,$(modules)) main.pdf
%.agdai: %.lagda
	agda -i . -i ${AGDALIBDIR} $< 
main.pdf: $(addsuffix .lagda,$(modules)) main.lagda 
	latexmk -pdf -g main.lagda
