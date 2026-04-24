
Require Import CData.

From Stdlib Require Import List.
Import ListNotations.

Module VT (Data : CDATA).
  Import Data.

  Inductive VirtualTree : Set := (* the actal tree with root, branch, node and leaf *)
  | Seed
  | Node (data: Data.t) (child: VirtualTree)
  | Branch (l: VirtualTree) (r: VirtualTree)
  | Leaf (id: nat).

  (* is valid : node child is not a node, any child is not a root *)
  

  Fixpoint is_valid_tree_structure (t: VirtualTree) : Prop :=
    match t with
    | Seed => True
    | Node _ c => match c with
                  | Seed => False
                  | Node _ _ => False
                  | _ => is_valid_tree_structure c
                  end
    | Branch l r => match l, r with
                    | Seed, _ => False
                    | _, Seed => False
                    | _, _ => (is_valid_tree_structure l) /\ (is_valid_tree_structure r)
                    end
    | Leaf _ => True
    end.

  Fixpoint get_all_ids (t: VirtualTree) : list nat :=
    match t with
    | Seed => []
    | Node d c => get_all_ids c
    | Branch l r => (get_all_ids l) ++ (get_all_ids r)
    | Leaf id => [id]
    end.

  Definition is_valid_tree_ids (t: VirtualTree) : Prop := NoDup (get_all_ids t).

  Definition is_valid_tree (t: VirtualTree) : Prop :=
    is_valid_tree_structure t /\ is_valid_tree_ids t.

  Fixpoint max_id_in_tree (t: VirtualTree) : nat :=
    match t with
    | Seed => 0 (*removed the option for cleaner split *)
    | Node _ c => max_id_in_tree c
    | Branch l r => Nat.max (max_id_in_tree l) (max_id_in_tree r)
    (*match (max_id_in_tree l), (max_id_in_tree r) with
                    | Some vl, Some vr => Some (Nat.max vl vr)
                    | Some vl, _ => Some vl
                    | _, Some vr => Some vr
                    | _, _ => None
                    end*)
    | Leaf i => i
    end.
    

  (* Type state: counter + tree (+ param ?) *)
  (* Define validity for a state *)

  Definition State := (VirtualTree * Data.p)%type. (* TODO remove counter *)

  Definition tree (s: State) : VirtualTree :=
    match s with
    | (t, _) => t
    end.
  (*Definition cnt (s: State) : nat :=
    match s with
    | (_, c, _) => c
    end.*)
  Definition param (s: State) : Data.p :=
    match s with
    | (_, p) => p
    end.

  (* TODO : is_valid_state : max index in tree is less that counter, and tree is valid *)
  Definition is_valid_state (s: State) : Prop :=
    is_valid_tree_structure (tree s) /\ is_valid_tree_ids (tree s).
  

  Definition is_leaf_with_id (t: VirtualTree) (id: nat) : bool :=
    match t with
    | Leaf i => Nat.eqb i id
    | _ => false
    end.

  Definition empty (param: Data.p) : State :=
    (Seed, param).

  Definition with_one_leaf (param: Data.p) : State :=
    (Leaf 0, param).

  Fixpoint insert_in_tree (id: nat) (new: Data.t) (t: VirtualTree) : VirtualTree :=
    match t with
    | Seed => Seed
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
    (insert_in_tree id new (tree s), param s).

  Fixpoint split_in_tree (id: nat) (new_id: nat) (t: VirtualTree) : VirtualTree :=
    match t with
    | Seed => Seed
    | Node d c => Node d (split_in_tree id new_id c)
    | Branch l r => Branch (split_in_tree id new_id l) (split_in_tree id new_id r)
    | Leaf i => if Nat.eqb i id
                then Branch (Leaf i) (Leaf id)
                else Leaf i
    end.

  Definition split (id: nat) (s: State) : State * nat :=
    let t:= tree s in
    let new_id := (max_id_in_tree t) + 1 in
    ((split_in_tree id new_id t, param s), new_id).

  Fixpoint is_branch_with_id (id : nat) (t: VirtualTree) : bool :=
    match t with
    | Seed => false
    | Node _ c => is_branch_with_id id c
    | Branch _ _ => false
    | Leaf i => Nat.eqb i id
    end.

  Fixpoint delete_in_tree (id : nat) (t: VirtualTree) : VirtualTree :=
    match t with
    | Seed => Seed
    | Node d c =>
        let c' := delete_in_tree id c in
        match c' with
        | Seed => Seed
        | Branch _ _ => Node d c'
        | Node d'' c'' => Node (Data.compress d d'') c''
        | Leaf i => Node d c'
        end
    | Branch l r => if (is_branch_with_id id l) (*could define it like node instead *)
                    then r
                    else if (is_branch_with_id id r)
                         then l
                         else Branch (delete_in_tree id l) (delete_in_tree id r)
    | Leaf i => if Nat.eqb i id
                then Seed
                else Leaf i
    end.

  Definition delete (id: nat) (s: State) :=
    (delete_in_tree id (tree s), param s).

  Inductive triple_option (A: Type) :=
  | TNone
  | TEmpty
  | TSome (v: A).
  Arguments TNone {A}.
  Arguments TEmpty {A}.
  Arguments TSome {A}.

  Fixpoint get_compressed_data_in_tree (id: nat) (t: VirtualTree) : triple_option Data.t :=
    match t with
    | Seed => TNone
    | Node d c =>
        match get_compressed_data_in_tree id c with
        | TNone => TNone
        | TEmpty => TSome d
        | TSome v => TSome (Data.compress d v)
        end
    | Branch l r =>
        match (get_compressed_data_in_tree id l) with
        | TNone => match (get_compressed_data_in_tree id r) with
                  | TNone => TNone
                  | TEmpty => TEmpty
                  | TSome v => TSome v
                  end
        | TEmpty => TEmpty
        | TSome v => TSome v
        end
    | Leaf i => if Nat.eqb i id
                then TEmpty
                else TNone
    end.

  Definition get_compressed_data (id:nat) (s: State) : option Data.t :=
    match get_compressed_data_in_tree id (tree s) with
    | TSome v => Some v
    | _ => None
    end.

  Definition is_empty_tree (t: VirtualTree) : bool :=
    match t with
    | Seed => true
    | _ => false
    end.



  (* Keep seed (for now), remove counter *)
  (* Proving todo *)

  (* Insert : insert seed -> seed
    is_invalid_state and is_valid input id, get on id = compress (get id oldtree, new data) /\ get on i not id = same as before, is_valid new tree *)

  (* split: is valid old state, is valid id -> is valid new state and is valid id and new id on new state *)
  (* get on id = get on new id *) (* get on other ids unchanged *)

  (* delete : preconds -> not is valid id on new tree, get on all other ids unchanged. *)

  (* TODO add to validity: define validity for CData and check for each node *)

End VT.
