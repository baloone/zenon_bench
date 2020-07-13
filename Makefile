OPS := $(shell find . -name "*.p")

.PHONY: all $(OPS)

all: $(OPS)

$(OPS):%.p:
	./run.sh $* >> res.js




