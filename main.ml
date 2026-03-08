
open Virtual_tree

let () =
  let param = read_int() in
  let module IntTree = Virtual_tree(struct
    type t = int
    let compress = fun x y -> max (x + y) param
  end) in
  let tree = IntTree.empty() in
  print_endline "created a tree"