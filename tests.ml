
open Virtual_tree

module IntData = struct
  type t = int
  let compress = fun x y -> max x y
  let to_string = string_of_int
end

module IntTree = Virtual_tree(IntData)

module Tests: sig 
  val tests : unit -> unit
end = struct

  let empty_test () =
    let empty_tree = IntTree.empty() in
    assert(IntTree.is_empty empty_tree);
    IntTree.delete empty_tree;
    assert(IntTree.is_empty empty_tree)

  let tests () = 
    Printf.printf "\027[32mTests: \027[0m\n\n";
    empty_test();
    Printf.printf "\027[32mTests passed\027[0m\n"
end

let () =
  Tests.tests()