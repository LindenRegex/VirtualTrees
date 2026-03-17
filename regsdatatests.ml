
open Regsdata

module Tests: sig 
  val tests : unit -> unit
end = struct

  let neutral_test () = 
    assert(Regsdata.neutral_element = Incomplete([]))

  let tests () = 
    Printf.printf "\027[32mTests: \027[0m\n\n";
    neutral_test();
    Printf.printf "\027[32mTests passed\027[0m\n"
end

let () =
  Tests.tests()