OCAMLC = ocamlc
TARGET = main
SOURCES = virtual_tree.ml main.ml

all: $(TARGET)

$(TARGET): $(SOURCES)
	$(OCAMLC) -o $(TARGET) virtual_tree.ml main.ml

clean:
	rm -f *.cmi *.cmo $(TARGET)