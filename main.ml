
open Virtual_tree

let () =
  let param = read_int() in
  let module IntTree = Virtual_tree(struct
    type t = int
    type p = int
    let neutral_element = 0
    let compress = fun p x y -> max p (x + y)
    let to_string = string_of_int
  end) in
  let tree0 = IntTree.empty param in
  IntTree.print tree0;
  IntTree.insert tree0 5;
  IntTree.print tree0;
  let tree1 = IntTree.split tree0 in
  print_endline "splitted";
  IntTree.print tree0;
  IntTree.print tree1;
  IntTree.insert tree1 9;
  print_endline "added 9 in tree1";
  IntTree.print tree0;
  IntTree.print tree1;
  IntTree.insert tree1 100;
  print_endline "added 100 in tree 1";
  IntTree.print tree0;
  IntTree.print tree1;
  IntTree.insert tree0 0;
  print_endline "added 0 in tree 0";
  IntTree.print tree0;
  IntTree.print tree1;
  IntTree.insert tree0 1;
  print_endline "added 1 in tree 0";
  IntTree.print tree0;
  IntTree.print tree1;
  IntTree.delete tree0;
  print_endline "deleted tree 0";
  IntTree.print tree0; (*garbage*)
  IntTree.print tree1