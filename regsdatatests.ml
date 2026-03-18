
open Regsdata

module Tests: sig 
  val tests : unit -> unit
end = struct

  let neutral_test () = 
    assert(Regsdata.neutral_element = Incomplete([]))

  let two_arrays_test0 () =
    let a_old = Regsdata.Complete({a_cp=[|1; 2; 3; 4|]; a_clk=[|5; 6; 7; 8|]}) in
    let a_new = Regsdata.Complete({a_cp=[|9; 10; 11; 12|]; a_clk=[|13; 14; 15; 16|]}) in
    let a = Regsdata.compress a_old a_new in
    assert(a = a_new);
    assert(a = a_old) (* because old is mutated *)

  let two_arrays_test1 () =
    let a_old = Regsdata.Complete({a_cp=[|1; 2; -1; 4|]; a_clk=[|-1; 6; 7; -1|]}) in
    let a_new = Regsdata.Complete({a_cp=[|9; 10; 11; -1|]; a_clk=[|-1; 14; -1; 16|]}) in
    let a = Regsdata.compress a_old a_new in
    assert(a = Regsdata.Complete({a_cp=[|9; 10; 11; 4|]; a_clk=[|-1; 14; 7; 16|]}));
    assert(a = a_old) (* because old is mutated *)

  let two_lists_test0 () =
    let l_old = Regsdata.Incomplete([(1, 1, 1); (2, 2, 2)]) in
    let l_new = Regsdata.Incomplete([(3, 3, 3); (4, 4, 4)]) in
    let l = Regsdata.compress l_old l_new in
    assert (l = Regsdata.Incomplete([(3, 3, 3); (4, 4, 4); (1, 1, 1); (2, 2, 2)]))

  let tests () = 
    Printf.printf "\027[32mTests: \027[0m\n\n";
    neutral_test();
    two_arrays_test0();
    two_arrays_test1();
    two_lists_test0();
    Printf.printf "\027[32mTests passed\027[0m\n"
end

let () =
  Tests.tests()