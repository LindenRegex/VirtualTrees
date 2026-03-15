OCAMLC = ocamlc
SRC = virtual_tree.ml
MAIN_SRC = main.ml
TEST_SRC = tests.ml

MAIN = main
TEST = tests

all: $(MAIN) $(TEST)

$(MAIN): $(SRC) $(MAIN_SRC)
	$(OCAMLC) -o main $(SRC) $(MAIN_SRC)

$(TEST): $(SRC) $(TEST_SRC)
	$(OCAMLC) -o tests $(SRC) $(TEST_SRC)

clean:
	rm -f *.cmo *.cmi main tests