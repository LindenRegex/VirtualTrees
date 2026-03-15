
open Virtual_tree

module IntData = struct
  type t = int
  let neutral_element = 0
  let compress = fun x y -> x + y
  let to_string = string_of_int
end

module IntTree = Virtual_tree(IntData)

module Tests: sig 
  val tests : unit -> unit
end = struct

  let empty_test () =
    let empty_tree = IntTree.empty() in
    assert(IntTree.is_empty empty_tree);
    assert((IntTree.depth empty_tree) = 0);
    assert((IntTree.node_depth empty_tree) = 0);
    IntTree.delete empty_tree;
    assert(IntTree.is_empty empty_tree)

  let delete_single_branch_test () =
    let tree = IntTree.empty() in
    IntTree.insert tree 0;
    IntTree.insert tree 1;
    IntTree.delete tree;
    assert(IntTree.is_empty tree)

  let delete_other_child_is_branch_test () = 
    let tree0 = IntTree.empty() in
    let tree1 = IntTree.split tree0 in
    assert((IntTree.depth tree0) = 1);
    assert((IntTree.depth tree1) = 1);
    assert((IntTree.node_depth tree0) = 0);
    assert((IntTree.node_depth tree1) = 0);
    let tree2 = IntTree.split tree1 in
    assert((IntTree.depth tree0) = 1);
    assert((IntTree.depth tree1) = 2);
    assert((IntTree.depth tree2) = 2);
    assert((IntTree.node_depth tree0) = 0);
    assert((IntTree.node_depth tree1) = 0);
    assert((IntTree.node_depth tree2) = 0);
    IntTree.delete tree0;
    assert((IntTree.depth tree1) = 1);
    assert((IntTree.depth tree2) = 1);
    assert((IntTree.node_depth tree1) = 0);
    assert((IntTree.node_depth tree2) = 0)

  let get_data_single_branch () = 
    let tree = IntTree.empty() in
    IntTree.insert tree 3;
    assert((IntTree.depth tree) = 1);
    assert((IntTree.node_depth tree) = 1);
    IntTree.insert tree 4;
    assert((IntTree.depth tree) = 1);
    assert((IntTree.node_depth tree) = 1);
    IntTree.insert tree 5;
    assert((IntTree.depth tree) = 1);
    assert((IntTree.node_depth tree) = 1);
    IntTree.insert tree 6;
    assert((IntTree.depth tree) = 1);
    assert((IntTree.node_depth tree) = 1);
    assert((IntTree.get_data tree) = 18)


  let tests () = 
    Printf.printf "\027[32mTests: \027[0m\n\n";
    empty_test();
    delete_single_branch_test();
    delete_other_child_is_branch_test();
    get_data_single_branch();
    Printf.printf "\027[32mTests passed\027[0m\n"
end

let () =
  Tests.tests()