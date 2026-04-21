
Require Import CData.

Module VT (Data : CDATA).
  Import Data.

  Inductive VirtualTree : Set := (* the actal tree with root, branch, node and leaf *)
  | Root (child: VirtualTree)
  | Node (data: Data.t) (child: VirtualTree)
  | Branch (l: VirtualTree) (r: VirtualTree)
  | Leaf (id: nat).
    

  (* Type state: counter + tree (+ param ?) *)
  (* Definine validity for a state *)

  Definition State := (VirtualTree * nat * Data.p)%type.

  Definition tree (s: State) : VirtualTree :=
    match s with
    | (t, _, _) => t
    end.
  Definition cnt (s: State) : nat :=
    match s with
    | (_, c, _) => c
    end.
  Definition param (s: State) : Data.p :=
    match s with
    | (_, _, p) => p
    end.

  Definition is_leaf_with_id (t: VirtualTree) (id: nat) : bool :=
    match t with
    | Leaf i => Nat.eqb i id
    | _ => false
    end.

  Definition empty (param: Data.p) : State :=
    (Root(Leaf(0)), 1, param).

  Fixpoint insert_in_tree (id: nat) (new: Data.t) (t: VirtualTree) : VirtualTree :=
    match t with
    | Root c => if is_leaf_with_id c id
                then Root (Node new c)
                else Root (insert_in_tree id new c)
    | Node d c => if is_leaf_with_id c id
                  then Node (Data.compress d new) c
                  else Node d (insert_in_tree id new c)
    | Branch l r => if is_leaf_with_id l id
                    then Branch (Node new l) r
                    else if is_leaf_with_id r id
                         then Branch l (Node new r)
                         else Branch (insert_in_tree id new l) (insert_in_tree id new r)
    | Leaf i => t
    end.

  Definition insert (id: nat) (new : Data.t) (s: State) : State :=
    (insert_in_tree id new (tree s), cnt s, param s).

  Fixpoint split_in_tree (id: nat) (new_id: nat) (t: VirtualTree) : VirtualTree :=
    match t with
    | Root c => Root (split_in_tree id new_id c)
    | Node d c => Node d (split_in_tree id new_id c)
    | Branch l r => Branch (split_in_tree id new_id l) (split_in_tree id new_id r)
    | Leaf i => Branch (Leaf i) (Leaf id)
    end.

  Definition split (id: nat) (s: State) : State * nat :=
    ((split_in_tree id (cnt s) (tree s), (cnt s) + 1, param s), cnt s).

  Definition delete := Admitted.

  Definition get_compressed_data := Admitted.

  Definition is_empty := Admitted.

End VT.
