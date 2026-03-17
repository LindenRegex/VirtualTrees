OCAMLC = ocamlc
SRC = virtual_tree.ml
MAIN_SRC = main.ml
TEST_SRC = tests.ml
REGS_SRC = regsdata.ml regsdatatests.ml

MAIN = main
TEST = tests
REGS = regstests

all: $(MAIN) $(TEST)
regs : $(REGS)

$(MAIN): $(SRC) $(MAIN_SRC)
	$(OCAMLC) -o $(MAIN) $(SRC) $(MAIN_SRC)

$(TEST): $(SRC) $(TEST_SRC)
	$(OCAMLC) -o $(TEST) $(SRC) $(TEST_SRC)

$(REGS): $(REGS_SRC)
	$(OCAMLC) -o $(REGS) $(REGS_SRC)

clean:
	rm -f *.cmo *.cmi $(MAIN) $(TEST) $(REGS)