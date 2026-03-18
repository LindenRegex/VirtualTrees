
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

  let two_lists_test1 () =
    let l_old = Regsdata.Incomplete([(1, 1, 1); (2, 2, 2)]) in
    let l_new = Regsdata.Incomplete([(3, 3, 3); (4, 4, 4); (0, 0, 0)]) in
    let l = Regsdata.compress l_old l_new in
    assert (l = Regsdata.Complete({a_cp=[|0; 1; 2; 3; 4|]; a_clk=[|0; 1; 2; 3; 4|]}))

  let two_lists_test2 () =
    let l_old = Regsdata.Incomplete([(1, 1, 1); (2, 2, 2)]) in
    let l_new = Regsdata.Incomplete([(3, 3, 3); (4, 4, 4); (1, 0, 0)]) in
    let l = Regsdata.compress l_old l_new in
    assert (l = Regsdata.Complete({a_cp=[|-1; 0; 2; 3; 4|]; a_clk=[|-1; 0; 2; 3; 4|]}))

  let two_lists_test3 () =
    let l_old = Regsdata.Incomplete([(1, 1, 1); (2, 5, 5); (2, 2, 2); (1, 7, 7)]) in
    let l_new = Regsdata.Incomplete([(3, 6, 6); (1, 0, 0); (3, 3, 3)]) in
    let l = Regsdata.compress l_old l_new in
    assert (l = Regsdata.Complete({a_cp=[|-1; 0; 5; 6; -1|]; a_clk=[|-1; 0; 5; 6; -1|]}))

  let list_array_test0 () = 
    let a_old = Regsdata.Complete({a_cp=[|1; 2; 3; 4; 5|]; a_clk=[|6; 7; 8; 9; 10|]}) in
    let l_new = Regsdata.Incomplete([(0, 0, 0); (0, 11, 11); (3, 12, 12)]) in
    let l = Regsdata.compress a_old l_new in
    assert (l = Regsdata.Complete({a_cp=[|0; 2; 3; 12; 5|]; a_clk=[|0; 7; 8; 12; 10|]}))
  
  let list_array_test1 () = 
    let a_old = Regsdata.Complete({a_cp=[|1; 2; 3; -1; -1|]; a_clk=[|6; 7; 8; -1; -1|]}) in
    let l_new = Regsdata.Incomplete([(0, -1, 0); (3, 11, -1); (3, 12, 12)]) in
    let l = Regsdata.compress a_old l_new in
    assert (l = Regsdata.Complete({a_cp=[|1; 2; 3; 11; -1|]; a_clk=[|0; 7; 8; 12; -1|]}))

  let array_list_test0 () = 
    let l_old = Regsdata.Incomplete([(0, 0, 0); (3, 11, 11); (3, 12, 12)]) in
    let a_new = Regsdata.Complete({a_cp=[|1; 2; 3; 4; 5|]; a_clk=[|6; 7; 8; 9; 10|]}) in
    let l = Regsdata.compress l_old a_new in
    assert (l = Regsdata.Complete({a_cp=[|1; 2; 3; 4; 5|]; a_clk=[|6; 7; 8; 9; 10|]}))

  let array_list_test1 () = 
    let l_old = Regsdata.Incomplete([(0, 0, 0); (3, 11, 11); (3, 12, 12)]) in
    let a_new = Regsdata.Complete({a_cp=[|1; 2; 3; 4; -1|]; a_clk=[|6; 7; 8; 9; -1|]}) in
    let l = Regsdata.compress l_old a_new in
    assert (l = Regsdata.Complete({a_cp=[|1; 2; 3; 4; -1|]; a_clk=[|6; 7; 8; 9; -1|]}))

  let array_list_test2 () = 
    let l_old = Regsdata.Incomplete([(0, 0, 0); (3, 11, 11); (3, 12, 12)]) in
    let a_new = Regsdata.Complete({a_cp=[|1; 2; 3; -1; -1|]; a_clk=[|6; 7; 8; -1; -1|]}) in
    let l = Regsdata.compress l_old a_new in
    assert (l = Regsdata.Complete({a_cp=[|1; 2; 3; 11; -1|]; a_clk=[|6; 7; 8; 11; -1|]}))

  let array_list_test3 () = 
    let l_old = Regsdata.Incomplete([(0, -1, 0); (3, 11, 11); (3, 12, 12); (1, 13, 13)]) in
    let a_new = Regsdata.Complete({a_cp=[|1; -1; 3; -1; -1|]; a_clk=[|6; 7; 8; 9; -1|]}) in
    let l = Regsdata.compress l_old a_new in
    assert (l = Regsdata.Complete({a_cp=[|1; 13; 3; 11; -1|]; a_clk=[|6; 7; 8; 9; -1|]}))

  let tests () = 
    Printf.printf "\027[32mTests: \027[0m\n\n";
    neutral_test();
    two_arrays_test0();
    two_arrays_test1();
    two_lists_test0();
    two_lists_test1();
    two_lists_test2();
    two_lists_test3();
    list_array_test0();
    list_array_test1();
    array_list_test0();
    array_list_test1();
    array_list_test2();
    array_list_test3();
    Printf.printf "\027[32mTests passed\027[0m\n"
end

let () =
  Tests.tests()