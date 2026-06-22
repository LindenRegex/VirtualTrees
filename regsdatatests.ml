
open Regsdata

module Tests: sig 
  val tests : unit -> unit
end = struct

  let two_arrays_test0 () =
    let a_old = Regsdata.Complete({a_cp=[|1; 2; 3; 4|]; a_clk=[|5; 6; 7; 8|]}) in
    let a_new = Regsdata.Complete({a_cp=[|9; 10; 11; 12|]; a_clk=[|13; 14; 15; 16|]}) in
    let a = Regsdata.compress 4 a_old a_new in
    assert(a = a_new);
    assert(a = a_old) (* because old is mutated *)

  let two_arrays_test1 () =
    let a_old = Regsdata.Complete({a_cp=[|1; -2; -1; 4|]; a_clk=[|-1; 6; -2; -1|]}) in
    let a_new = Regsdata.Complete({a_cp=[|9; 10; 11; -1|]; a_clk=[|-1; 14; -1; 16|]}) in
    let a = Regsdata.compress 4 a_old a_new in
    assert(a = Regsdata.Complete({a_cp=[|9; 10; 11; -1|]; a_clk=[|-1; 14; -1; 16|]}));
    assert(a = a_old) (* because old is mutated *)

  let two_arrays_test2 () =
    let a_old = Regsdata.Complete({a_cp=[|1; 2; -1; 4|]; a_clk=[|-2; 6; 7; -2|]}) in
    let a_new = Regsdata.Complete({a_cp=[|9; 10; 11; -2|]; a_clk=[|-2; -2; -1; 16|]}) in
    let a = Regsdata.compress 4 a_old a_new in
    assert(a = Regsdata.Complete({a_cp=[|9; 10; 11; 4|]; a_clk=[|-2; 6; -1; 16|]}));
    assert(a = a_old) (* because old is mutated *)

  let two_lists_test0 () =
    let l_old = Regsdata.Incomplete({size=2; l=[(1, 1, 1); (2, 2, 2)]}) in
    let l_new = Regsdata.Incomplete({size=2; l=[(3, 3, 3); (4, 4, 4)]}) in
    let l = Regsdata.compress 5 l_old l_new in
    assert (l = Regsdata.Incomplete({size=4; l=[(3, 3, 3); (4, 4, 4); (1, 1, 1); (2, 2, 2)]}))

  let two_lists_test1 () =
    let l_old = Regsdata.Incomplete({size=2; l=[(1, 1, 1); (2, 2, 2)]}) in
    let l_new = Regsdata.Incomplete({size=3; l=[(3, 3, 3); (4, 4, 4); (0, 0, 0)]}) in
    let l = Regsdata.compress 5 l_old l_new in
    assert (l = Regsdata.Complete({a_cp=[|0; 1; 2; 3; 4|]; a_clk=[|0; 1; 2; 3; 4|]}))

  let two_lists_test2 () =
    let l_old = Regsdata.Incomplete({size=2; l=[(1, -1, -1); (2, 2, 2)]}) in
    let l_new = Regsdata.Incomplete({size=3; l=[(3, 3, 3); (4, 4, 4); (1, 0, 0)]}) in
    let l = Regsdata.compress 5 l_old l_new in
    assert (l = Regsdata.Complete({a_cp=[|-2; 0; 2; 3; 4|]; a_clk=[|-2; 0; 2; 3; 4|]}))

  let two_lists_test3 () =
    let l_old = Regsdata.Incomplete({size=4; l=[(1, 1, 1); (2, 5, 5); (2, 2, 2); (1, 7, 7)]}) in
    let l_new = Regsdata.Incomplete({size=3; l=[(3, -1, -1); (1, 0, 0); (3, 3, 3)]}) in
    let l = Regsdata.compress 5 l_old l_new in
    assert (l = Regsdata.Complete({a_cp=[|-2; 0; 5; -1; -2|]; a_clk=[|-2; 0; 5; -1; -2|]}))

  let two_lists_test4 () =
    let l_old = Regsdata.Incomplete({size=4; l=[(1, 1, 1); (2, 5, 5); (2, 2, 2); (1, 7, 7)]}) in
    let l_new = Regsdata.Incomplete({size=3; l=[(3, -2, -2); (1, 0, 0); (3, 3, 3)]}) in
    let l = Regsdata.compress 5 l_old l_new in
    assert (l = Regsdata.Complete({a_cp=[|-2; 0; 5; 3; -2|]; a_clk=[|-2; 0; 5; 3; -2|]}))

  let list_array_test0 () = 
    let a_old = Regsdata.Complete({a_cp=[|-2; 2; 3; 4; 5|]; a_clk=[|6; 7; 8; 9; 10|]}) in
    let l_new = Regsdata.Incomplete({size=3; l=[(0, 0, 0); (0, 11, 11); (3, 12, 12)]}) in
    let l = Regsdata.compress 5 a_old l_new in
    assert (l = Regsdata.Complete({a_cp=[|0; 2; 3; 12; 5|]; a_clk=[|0; 7; 8; 12; 10|]}))
  
  let list_array_test1 () = 
    let a_old = Regsdata.Complete({a_cp=[|1; 2; 3; -1; -1|]; a_clk=[|6; 7; 8; -1; -1|]}) in
    let l_new = Regsdata.Incomplete({size=3; l=[(0, -1, 0); (3, 11, -1); (3, 12, 12)]}) in
    let l = Regsdata.compress 5 a_old l_new in
    assert (l = Regsdata.Complete({a_cp=[|-1; 2; 3; 11; -1|]; a_clk=[|0; 7; 8; -1; -1|]}))

  let list_array_test2 () = 
    let a_old = Regsdata.Complete({a_cp=[|1; 2; 3; -1; -1|]; a_clk=[|6; 7; 8; -1; -1|]}) in
    let l_new = Regsdata.Incomplete({size=3; l=[(0, -2, 0); (3, 11, -2); (3, 12, 12)]}) in
    let l = Regsdata.compress 5 a_old l_new in
    assert (l = Regsdata.Complete({a_cp=[|1; 2; 3; 11; -1|]; a_clk=[|0; 7; 8; 12; -1|]}))

  let array_list_test0 () = 
    let l_old = Regsdata.Incomplete({size=3; l=[(0, 0, 0); (3, 11, 11); (3, 12, 12)]}) in
    let a_new = Regsdata.Complete({a_cp=[|1; 2; 3; 4; 5|]; a_clk=[|6; 7; 8; 9; 10|]}) in
    let l = Regsdata.compress 5 l_old a_new in
    assert (l = Regsdata.Complete({a_cp=[|1; 2; 3; 4; 5|]; a_clk=[|6; 7; 8; 9; 10|]}))

  let array_list_test1 () = 
    let l_old = Regsdata.Incomplete({size=3; l=[(0, 0, 0); (3, 11, 11); (3, 12, 12)]}) in
    let a_new = Regsdata.Complete({a_cp=[|1; 2; 3; 4; -1|]; a_clk=[|6; 7; 8; 9; -1|]}) in
    let l = Regsdata.compress 5 l_old a_new in
    assert (l = Regsdata.Complete({a_cp=[|1; 2; 3; 4; -1|]; a_clk=[|6; 7; 8; 9; -1|]}))

  let array_list_test2 () = 
    let l_old = Regsdata.Incomplete({size=3; l=[(0, 0, 0); (3, 11, 11); (3, 12, 12)]}) in
    let a_new = Regsdata.Complete({a_cp=[|1; 2; 3; -1; -1|]; a_clk=[|6; 7; 8; -1; -1|]}) in
    let l = Regsdata.compress 5 l_old a_new in
    assert (l = Regsdata.Complete({a_cp=[|1; 2; 3; -1; -1|]; a_clk=[|6; 7; 8; -1; -1|]}))

  let array_list_test3 () = 
    let l_old = Regsdata.Incomplete({size=4; l=[(0, -1, 0); (3, -2, -2); (3, 12, 12); (1, 13, 13)]}) in
    let a_new = Regsdata.Complete({a_cp=[|1; -1; 3; -1; -1|]; a_clk=[|6; 7; 8; 9; -1|]}) in
    let l = Regsdata.compress 5 l_old a_new in
    assert (l = Regsdata.Complete({a_cp=[|1; -1; 3; -1; -1|]; a_clk=[|6; 7; 8; 9; -1|]}))

  let array_list_test4 () = 
    let l_old = Regsdata.Incomplete({size=3; l=[(0, 0, 0); (3, 11, 11); (3, 12, 12)]}) in
    let a_new = Regsdata.Complete({a_cp=[|1; 2; 3; 4; -2|]; a_clk=[|6; 7; 8; 9; -2|]}) in
    let l = Regsdata.compress 5 l_old a_new in
    assert (l = Regsdata.Complete({a_cp=[|1; 2; 3; 4; -2|]; a_clk=[|6; 7; 8; 9; -2|]}))

  let array_list_test5 () = 
    let l_old = Regsdata.Incomplete({size=3; l=[(0, 0, 0); (3, 11, 11); (3, 12, 12)]}) in
    let a_new = Regsdata.Complete({a_cp=[|1; 2; 3; -2; -2|]; a_clk=[|6; 7; 8; -2; -2|]}) in
    let l = Regsdata.compress 5 l_old a_new in
    assert (l = Regsdata.Complete({a_cp=[|1; 2; 3; 11; -2|]; a_clk=[|6; 7; 8; 11; -2|]}))

  let array_list_test6 () = 
    let l_old = Regsdata.Incomplete({size=4; l=[(0, -2, 0); (3, 11, 11); (3, 12, 12); (1, 13, 13)]}) in
    let a_new = Regsdata.Complete({a_cp=[|1; -2; 3; -2; -2|]; a_clk=[|6; 7; 8; 9; -2|]}) in
    let l = Regsdata.compress 5 l_old a_new in
    assert (l = Regsdata.Complete({a_cp=[|1; 13; 3; 11; -2|]; a_clk=[|6; 7; 8; 9; -2|]}))

  let array_get_test () = 
    let a = Regsdata.Complete({a_cp=[|1; 5; 3; 9; -1|]; a_clk=[|-2; 7; 8; 9; -1|]}) in
    assert ((Regsdata.get_cp_at a 1) = 5);
    assert ((Regsdata.get_cp_at a 4) = -1);
    assert ((Regsdata.get_clk_at a 2) = 8);
    assert ((Regsdata.get_clk_at a 0) = -2)

  let list_get_test () = 
    let l = Regsdata.Incomplete({size=3; l=[(0, 0, 1); (3, -1, -2); (3, 12, 13)]}) in
    assert ((Regsdata.get_cp_at l 0) = 0);
    assert ((Regsdata.get_cp_at l 3) = -1);
    assert ((Regsdata.get_cp_at l 4) = -2);
    assert ((Regsdata.get_clk_at l 0) = 1);
    assert ((Regsdata.get_clk_at l 3) = -2);
    assert ((Regsdata.get_clk_at l 1) = -2)

  let tests () = 
    Printf.printf "\027[32mTests: \027[0m\n\n";
    two_arrays_test0();
    two_arrays_test1();
    two_arrays_test2();
    two_lists_test0();
    two_lists_test1();
    two_lists_test2();
    two_lists_test3();
    two_lists_test4();
    list_array_test0();
    list_array_test1();
    list_array_test2();
    array_list_test0();
    array_list_test1();
    array_list_test2();
    array_list_test3();
    array_list_test4();
    array_list_test5();
    array_list_test6();
    array_get_test();
    list_get_test();
    Printf.printf "\027[32mTests passed\027[0m\n"
end

let () =
  Tests.tests()