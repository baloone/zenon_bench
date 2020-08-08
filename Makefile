OPS := $(shell find . -name "*.p")

.PHONY: all $(OPS)

all: $(OPS)
	echo "}" >> res.js

$(OPS):%.p: res.js
	./run.sh $* >> res.js

res.js: 
	echo "module.exports={" >> res.js
	


