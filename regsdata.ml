
open Array

module Regsdata : sig
  type t = 
  | Complete of {
      a_cp: int Array.t;
      a_clk: int Array.t
    }
  | Incomplete of (int * int *int) list

  val neutral_element : t
  val compress : t -> t -> t
  val to_string : t -> string
  val to_arrays : t -> int Array.t * int Array.t
end = struct

  let regs_size = 5 (* to change *)

  type t = 
  | Complete of {
      a_cp: int Array.t;
      a_clk: int Array.t
    } (*arrays*)

    (* first int: the key *)
    (* second int: the cp value *)
    (* third int: the clock value *)
  | Incomplete of (int * int *int) list (*list: single or doubly ?*)

  let neutral_element : t = Incomplete([])

  let to_string (v: t) : string =
    match v with 
    | Complete arrays ->
      let s = ref "" in
      for c = 0 to (Array.length arrays.a_cp)-1 do
        s := !s ^ string_of_int c ^ ": " ^ string_of_int (arrays.a_cp.(c)) ^ " | "
      done;
      !s
    | Incomplete l ->
      let rec to_string_rec (l:(int*int*int) list) : string =
      match l with
      | [] -> ""
      | (i,cp,clk)::l' ->
         "(" ^ string_of_int i ^ "," ^ string_of_int cp ^ ")::" ^ to_string_rec l'
      in
      to_string_rec l

  (* a2 is more recent than a1 *)
  let merge_arrays (a1_cp: int Array.t) (a2_cp: int Array.t) (a1_clk: int Array.t) (a2_clk: int Array.t) : int Array.t * int Array.t =
    (* update a1 *)
    let update_oldest_cp (i: int) (new_cp: int): unit =
      if (new_cp <> -1) then a1_cp.(i) <- new_cp
      else () in
    let update_oldest_clk (i: int) (new_clk: int): unit =
      if (new_clk <> -1) then a1_clk.(i) <- new_clk
      else () in

    Array.iteri update_oldest_cp a2_cp;
    Array.iteri update_oldest_clk a2_clk;
    (a1_cp, a1_clk)

  (* array is more recent than list: list cannot overwrite array *)
  let compress_arrays_and_list (a_cp: int Array.t) (a_clk: int Array.t) (l: (int * int * int) list) : int Array.t * int Array.t =
    let rec fill_array (l:(int*int*int) list) : unit =
        match l with
        | [] -> ()
        | (i,cp,clk)::l' ->
            (* only setting reg values that haven't been set yet *)
            if (a_cp.(i) = -1) then a_cp.(i) <- cp;
            if (a_clk.(i) = -1) then a_clk.(i) <- clk;
            fill_array l' in
    fill_array l;
    (a_cp, a_clk)

  (* list is more recent than array, list overwrites array *)
  (* Problem: how to know if we overwrite array or list ? *)
  (* Solution 1: use doubly linked list like in Théo's paper *)
  (* Solution 2: convert l to array and merge arrays *)
  let compress_list_and_arrays (a_cp: int Array.t) (a_clk: int Array.t) (l: (int * int * int) list): int Array.t * int Array.t =
    let (l_cp, l_clk) = compress_arrays_and_list (Array.make regs_size (-1)) (Array.make regs_size (-1)) l in
    merge_arrays a_cp l_cp a_clk l_clk

  (* t1 is "oldest", t2 is "most recent" *)
  let compress (t1: t) (t2: t): t = 
    match t1, t2 with
    | Complete a1, Complete a2 -> (* merge arrays *)
      let (a_cp, a_clk) = merge_arrays a1.a_cp a2.a_cp a1.a_clk a2.a_clk in
      Complete({a_cp=a_cp; a_clk=a_clk}) 
    | Complete a1, Incomplete l2 -> (* incorporate l2 in a1 *)
      let (a_cp, a_clk) = compress_list_and_arrays a1.a_cp a1.a_clk l2 in
      Complete({a_cp=a_cp; a_clk=a_clk}) 
    | Incomplete l1, Complete a2 -> (* incorporate l1 into a2*)
      let (a_cp, a_clk) = compress_arrays_and_list a2.a_cp a2.a_clk l1 in
      Complete({a_cp=a_cp; a_clk=a_clk}) 
    | Incomplete l1, Incomplete l2 ->
      (* concatenate *)
      let l = l2 @ l1 in 
      (* if result has size larger that |r|, convert to complete form *)
      if List.length l >= regs_size then (
        let (a_cp, a_clk) = compress_arrays_and_list (Array.make regs_size (-1)) (Array.make regs_size (-1)) l in
        Complete({a_cp=a_cp; a_clk=a_clk})
      ) else 
        Incomplete(l)

  let to_arrays (v: t) : int Array.t * int Array.t =
    match v with 
    | Complete arrays -> (arrays.a_cp, arrays.a_clk)
    | Incomplete l -> compress_arrays_and_list (Array.make regs_size (-1)) (Array.make regs_size (-1)) l

end