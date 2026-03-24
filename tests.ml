
open Virtual_tree

module IntData = struct
  type t = int
  type p = int
  let neutral_element = 0
  let compress = fun p x y -> x + y
  let to_string = string_of_int
end

module IntTree = Virtual_tree(IntData)

module Tests: sig 
  val tests : unit -> unit
end = struct

  let empty_test () =
    let empty_tree = IntTree.empty 0 in
    assert(IntTree.is_empty empty_tree);
    assert((IntTree.depth empty_tree) = 0);
    assert((IntTree.node_depth empty_tree) = 0);
    assert((IntTree.get_data empty_tree) = IntData.neutral_element);
    IntTree.delete empty_tree;
    assert(IntTree.is_empty empty_tree)

  let delete_single_branch_test () =
    let tree = IntTree.empty 0 in
    IntTree.insert tree 0;
    IntTree.insert tree 1;
    IntTree.delete tree;
    assert(IntTree.is_empty tree)

  let delete_other_child_is_branch_test () = 
    let tree0 = IntTree.empty 0 in
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

  let get_data_single_branch_test () = 
    let tree = IntTree.empty 0 in
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

  let get_data_two_branches_test () =
    let tree = IntTree.empty 0 in
    IntTree.insert tree 7;
    let tree0 = IntTree.split tree in
    IntTree.insert tree 90;
    assert((IntTree.get_data tree) = 97);
    assert((IntTree.get_data tree0) = 7);
    IntTree.insert tree0 23;
    assert((IntTree.get_data tree) = 97);
    assert((IntTree.get_data tree0) = 30);
    IntTree.insert tree0 2;
    assert((IntTree.get_data tree) = 97);
    assert((IntTree.get_data tree0) = 32)

  let get_data_four_branches_test () =
    let tree0 = IntTree.empty 0 in
    IntTree.insert tree0 1;
    let tree1 = IntTree.split tree0 in
    let tree2 = IntTree.split tree1 in
    IntTree.insert tree0 2;
    IntTree.insert tree1 3;
    IntTree.insert tree2 4;
    assert((IntTree.get_data tree0) = 3);
    assert((IntTree.get_data tree1) = 4);
    assert((IntTree.get_data tree2) = 5);
    let tree3 = IntTree.split tree0 in
    assert((IntTree.get_data tree0) = 3);
    assert((IntTree.get_data tree3) = 3);
    IntTree.insert tree0 5;
    IntTree.insert tree3 6;
    assert((IntTree.get_data tree0) = 8);
    assert((IntTree.get_data tree1) = 4);
    assert((IntTree.get_data tree2) = 5);
    assert((IntTree.get_data tree3) = 9)

  let get_data_delete_two_branches () =
    let tree0 = IntTree.empty 0 in
    IntTree.insert tree0 1;
    let tree1 = IntTree.split tree0 in
    IntTree.insert tree0 2;
    IntTree.insert tree1 3;
    IntTree.delete tree0;
    assert((IntTree.get_data tree1) = 4)

  let get_data_delete_four_branches () =
    let tree0 = IntTree.empty 0 in
    IntTree.insert tree0 1;
    let tree1 = IntTree.split tree0 in
    let tree2 = IntTree.split tree1 in
    IntTree.insert tree0 2;
    IntTree.insert tree1 3;
    IntTree.insert tree2 4;
    let tree3 = IntTree.split tree0 in
    IntTree.insert tree0 5;
    IntTree.insert tree3 6;
    IntTree.delete tree0;
    assert((IntTree.get_data tree1) = 4);
    assert((IntTree.get_data tree2) = 5);
    assert((IntTree.get_data tree3) = 9);
    IntTree.delete tree1;
    assert((IntTree.get_data tree2) = 5);
    assert((IntTree.get_data tree3) = 9);
    IntTree.delete tree2;
    assert((IntTree.get_data tree3) = 9)

  let tests () = 
    Printf.printf "\027[32mTests: \027[0m\n\n";
    empty_test();
    delete_single_branch_test();
    delete_other_child_is_branch_test();
    get_data_single_branch_test();
    get_data_two_branches_test();
    get_data_four_branches_test();
    get_data_delete_two_branches();
    get_data_delete_four_branches();
    Printf.printf "\027[32mTests passed\027[0m\n"
end

let () =
  Tests.tests()