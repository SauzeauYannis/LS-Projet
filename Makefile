SOURCES = projet.ml
EXEC = a.out
CAMLC = ocamlc

build: $(EXEC)

OBJS = $(SOURCES:.ml=.cmo)

$(EXEC): $(OBJS)
	$(CAMLC) -o $(EXEC) $(OBJS)

.SUFFIXES: .ml .cmo .cmi

.ml.cmo:
	$(CAMLC) -c $<

clean:
	rm -f *.cm[io]
	rm -f $(EXEC)