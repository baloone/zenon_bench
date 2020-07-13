OPS := $(shell find . -name "*.p")

.PHONY: all $(OPS)

all: $(OPS)
	echo "\n}" >> res.js

$(OPS):%.p: res.js
	./run.sh $* >> res.js

res.js: 
	echo "module.exports={\n" >> res.js
	


