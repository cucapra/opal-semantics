MAIN = opal

OBJS = ast.cmo lexer.cmo parser.cmo main.cmo

%.cmo : %.ml
	ocamlc -c -g $<

%.cmi: %.mli
	ocamlc -c -g $<

$(MAIN): $(OBJS)
	ocamlc -g -o $(MAIN) $(OBJS)

parser.ml: parser.mly
	ocamlyacc -q parser.mly
parser.mli: parser.ml

lexer.ml: lexer.mll
	ocamllex -q lexer.mll

clean:
	rm -f *.cmo *.cmi lexer.ml parser.ml parser.mli $(MAIN)

# Dependencies
depend: parser.ml parser.mli lexer.ml
	ocamldep *.mli *.ml > .depend
dep: depend

include .depend
