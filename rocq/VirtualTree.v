
Require Import CData.

Module VT (Data : CDATA).
  Import Data.

  Inductive VirtualTree : Set := (* the actal tree with root, branch, node and leaf *)
  | Seed
  | Root (child: VirtualTree)
  | Node (data: Data.t) (child: VirtualTree)
  | Branch (l: VirtualTree) (r: VirtualTree)
  | Leaf (id: nat).

  (* is valid : node child is not a node, any child is not a root *)
  

  Fixpoint is_valid_tree (t: VirtualTree) : bool :=
    match t with
    | Seed => true
    | Root c => match c with
                | Root _ => false
                | _ => is_valid_tree c
                end
    | Node _ c => match c with
                  | Root _ => false
                  | Node _ _ => false
                  | _ => is_valid_tree c
                  end
    | Branch l r => match l, r with
                    | Root _, _ => false
                    | _, Root _ => false
                    | _, _ => (is_valid_tree l) && (is_valid_tree r)
                    end
    | Leaf _ => true
    end.
    

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
    (Seed, 1, param).

  Definition with_one_leaf (param: Data.p) : State :=
    (Leaf 0, 1, param).

  Fixpoint insert_in_tree (id: nat) (new: Data.t) (t: VirtualTree) : VirtualTree :=
    match t with
    | Seed => Seed
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
    | Seed => Seed
    | Root c => Root (split_in_tree id new_id c)
    | Node d c => Node d (split_in_tree id new_id c)
    | Branch l r => Branch (split_in_tree id new_id l) (split_in_tree id new_id r)
    | Leaf i => Branch (Leaf i) (Leaf id)
    end.

  Definition split (id: nat) (s: State) : State * nat :=
    ((split_in_tree id (cnt s) (tree s), (cnt s) + 1, param s), cnt s).

  Fixpoint is_branch_with_id (id : nat) (t: VirtualTree) : bool :=
    match t with
    | Seed => false
    | Root c => is_branch_with_id id c
    | Node _ c => is_branch_with_id id c
    | Branch _ _ => false
    | Leaf i => Nat.eqb i id
    end.

  Fixpoint delete_in_tree (id : nat) (t: VirtualTree) : VirtualTree :=
    match t with
    | Seed => Seed
    | Root c => Root (delete_in_tree id c)
    | Node d c =>
        let c' := delete_in_tree id c in
        match c' with
        | Seed => Seed
        | Branch _ _ => Node d c'
        | Node d'' c'' => Node (Data.compress d d'') c''
        | Leaf i => Node d c'
        | _ => t
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
    (delete_in_tree id (tree s), cnt s, param s).

  Definition get_compressed_data := Admitted.

  Definition is_empty := Admitted.

End VT.
