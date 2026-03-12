
open Virtual_tree

let () =
  let param = read_int() in
  let module IntTree = Virtual_tree(struct
    type t = int
    let compress = fun x y -> max (x + y) param
    let to_string = string_of_int
  end) in
  let tree0 = IntTree.empty() in
  IntTree.print tree0;
  IntTree.insert tree0 5;
  IntTree.print tree0;
  let tree1 = IntTree.split tree0 in
  IntTree.print tree0;
  IntTree.print tree1;
  IntTree.insert tree1 9;
  IntTree.insert tree1 100;
  IntTree.insert tree0 0;
  IntTree.insert tree0 1;
  IntTree.print tree0;
  IntTree.print tree1;
  IntTree.delete tree0;
  IntTree.print tree1