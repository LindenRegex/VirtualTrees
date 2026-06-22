# Virtual Trees

**Author:** Mathilde Peruzzo

A virtual tree is a tree compressed to its minimal structure.

## OCaml implementation

The data structure is defined in virtual_tree.ml. main.ml is an example usage, with prints.

regsdata.ml is an example CData implementation, and the one used in RegElk.

To compile and run the tests :
```bash
make
./tests
./regstests
```

To run main:
```bash
./main
```
then enter a number.

## Formalization

Virtual trees and regsdata are formalized in rocq.

To compile:

```bash
cd rocq
make rocq
```