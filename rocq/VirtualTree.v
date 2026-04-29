
Require Import CData.

From Stdlib Require Import Arith Lia List.
Import ListNotations.

Module VT (Data : CDATA).
  Import Data.

  Inductive VirtualTree : Type := (* the actal tree with root, branch, node and leaf *)
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

  Fixpoint is_valid_id (t: VirtualTree) (id: nat) : Prop :=
    match t with
    | Seed => False
    | Node _ c => is_valid_id c id
    | Branch l r => is_valid_id l id \/ is_valid_id r id
    | Leaf i => i = id
    end.

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

  Fixpoint insert_in_tree (id: nat) (new: Data.t) (t: VirtualTree) (p: Data.p) : VirtualTree :=
    match t with
    | Seed => Seed
    | Node d c => if is_leaf_with_id c id
                  then Node (Data.compress p d new) c
                  else Node d (insert_in_tree id new c p)
    | Branch l r => if is_leaf_with_id l id
                    then Branch (Node new l) r
                    else if is_leaf_with_id r id
                         then Branch l (Node new r)
                         else Branch (insert_in_tree id new l p) (insert_in_tree id new r p)
    | Leaf i => t
    end.

  Definition insert (id: nat) (new : Data.t) (s: State) : State :=
    (insert_in_tree id new (tree s) (param s), param s).

  Fixpoint split_in_tree (id: nat) (new_id: nat) (t: VirtualTree) : VirtualTree :=
    match t with
    | Seed => Seed
    | Node d c => Node d (split_in_tree id new_id c)
    | Branch l r => Branch (split_in_tree id new_id l) (split_in_tree id new_id r)
    | Leaf i => if Nat.eqb i id
                then Branch (Leaf i) (Leaf new_id)
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

  Fixpoint delete_in_tree (id : nat) (t: VirtualTree) (p: Data.p) : VirtualTree :=
    match t with
    | Seed => Seed
    | Node d c =>
        let c' := delete_in_tree id c p in
        match c' with
        | Seed => Seed
        | Branch _ _ => Node d c'
        | Node d'' c'' => Node (Data.compress p d d'') c''
        | Leaf i => Node d c'
        end
    | Branch l r => if (is_branch_with_id id l) (*could define it like node instead *)
                    then r
                    else if (is_branch_with_id id r)
                         then l
                         else Branch (delete_in_tree id l p) (delete_in_tree id r p)
    | Leaf i => if Nat.eqb i id
                then Seed
                else Leaf i
    end.

  Definition delete (id: nat) (s: State) :=
    (delete_in_tree id (tree s) (param s), param s).

  Inductive triple_option (A: Type) :=
  | TNone
  | TEmpty
  | TSome (v: A).
  Arguments TNone {A}.
  Arguments TEmpty {A}.
  Arguments TSome {A}.

  (* TODO redefine top down *)
  Fixpoint get_compressed_data_in_tree (id: nat) (t: VirtualTree) (p: Data.p): triple_option Data.t :=
    match t with
    | Seed => TNone
    | Node d c =>
        match get_compressed_data_in_tree id c p with
        | TNone => TNone
        | TEmpty => TSome d
        | TSome v => TSome (Data.compress p d v)
        end
    | Branch l r =>
        match (get_compressed_data_in_tree id l p) with
        | TNone => match (get_compressed_data_in_tree id r p) with
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
    match get_compressed_data_in_tree id (tree s) (param s) with
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
    is_valid_state and is_valid input id, get on id = compress (get id oldtree, new data) /\ get on i not id = same as before, is_valid new tree *)
  
  (* the output state of insert is a valid state *)
  Lemma insert_valid : forall t p id d, (*might skip the t/p thing, and just use s*)
      is_valid_state (t, p) ->
      is_valid_id t id ->
      is_valid_state (insert id d (t, p)).
  Proof.
    intros t. induction t; intros p i d Hs Hi.
    - unfold insert.
      simpl.
      assumption.
    - unfold insert in *.
      simpl in *.
      destruct (is_leaf_with_id t0 i) eqn:L.
      (* TODO compress result is valid *)
      + unfold is_valid_state. unfold is_valid_state in Hs.
        destruct Hs as [Hs His]. simpl in *.
        split.
        * assumption.
        * unfold is_valid_tree_ids. unfold is_valid_tree_ids in His.
          simpl in *.
          assumption.
      + unfold is_valid_state. unfold is_valid_state in Hs.
        destruct Hs as [Hs His]. simpl in *.
        split.
        * destruct (insert_in_tree i d t0 p) eqn:Ti.
          -- admit. (* TODO: prove Ti cannot be Seed*)
          -- admit. (*TODO: prove Ti cannot be Node *)
          -- rewrite <- Ti.
             apply IHt; try assumption.
             unfold is_valid_state; simpl; split.
             ++ destruct t0; try contradiction; try assumption.
             ++ unfold is_valid_tree_ids in *. simpl in *. assumption.
          -- simpl. auto.
        * unfold is_valid_tree_ids. simpl.
          apply IHt.
          -- destruct t0; try contradiction.
             ++ unfold is_valid_state. unfold tree; split; try assumption.
             ++ unfold is_valid_state; simpl; split; auto.
          -- assumption.
    - unfold insert. simpl.
      destruct (is_leaf_with_id t1 i) eqn:L1; admit.
    - unfold insert. simpl.
      assumption.
  Admitted.

  (* when inserting for i, the new data for i is the compression of the compressed old data for i and the new data *)
  Lemma insert_correct1 : forall t p id d c_old c_new,
      is_valid_state (t, p) ->
      is_valid_id t id ->
      get_compressed_data id (t, p) = Some c_old -> (* case where data already existed for id *)
      get_compressed_data id (insert id d (t, p)) = Some c_new /\
        c_new = Data.compress p d c_old. (* TODO check compress order*)
  Admitted.

  (* when inserting for i with no data, the new data for i is the inserted data *)
  Lemma insert_correct2 : forall t p id d c,
      is_valid_state (t, p) ->
      is_valid_id t id ->
      get_compressed_data id (t, p) = None ->
      get_compressed_data id (insert id d (t, p)) = Some c.
  Admitted.

  (* the data for all other leaves is unchanged *)
  Lemma insert_correct3 : forall t p i j d o,
      is_valid_state (t, p) ->
      is_valid_id t i ->
      i <> j ->
      get_compressed_data j (t, p) = o ->
      get_compressed_data j (insert i d (t, p)) = o.
  Admitted.

  Lemma no_dup_one {A} : forall (x: A),
      NoDup [x].
  Proof.
    intros x.
    constructor.
    - intros H.
      apply in_nil in H.
      contradiction.
    - constructor.
  Qed.

  (* split: is valid old state, is valid id -> is valid new state and is valid id and new id on new state *)
  (* get on id = get on new id *) (* get on other ids unchanged *)

  (* the output state of split is valid, and the new id is valid on that tree *)
  Lemma split_valid : forall t p id,
      is_valid_state (t, p) ->
      is_valid_id t id ->
      let (s', j) := split id (t, p) in
      is_valid_state s' /\ is_valid_id (tree s') j.
  Proof.
    intros t. induction t; intros p i Hs Hi.
    - simpl in *. contradiction.
    - simpl. (* TODO: need split result is either branch or what was before *)
      split.
      + unfold is_valid_state. simpl. admit.
      + admit.
    - simpl. admit.
    - simpl.
      destruct (Nat.eqb id i) eqn:I; split; simpl.
      + unfold is_valid_state.
        split; simpl; try auto.
        unfold is_valid_tree_ids. simpl.
        constructor.
        * intros H. inversion H; subst; try lia.
          apply in_nil in H0. contradiction.
        * apply no_dup_one.
      + right. reflexivity.
      + assumption.
      + unfold is_valid_id in Hi.
        apply Nat.eqb_neq in I. lia.    
  Admitted.

  (* when splitting a leaf i, the resulting new leaves have the same compressed data as i *)
  Lemma split_correct1 : forall t p i o,
      is_valid_state (t, p) ->
      is_valid_id t i ->
      get_compressed_data i (t, p) = o ->
      let (s', j) := split i (t, p) in
      get_compressed_data i s' = o /\ get_compressed_data j s' = o.
  Admitted.

  (* when splitting leaf i, all other leaves have unchanged data *)
  Lemma split_correct2: forall t p i j o, (*might merge this one with the previous one *)
      is_valid_state (t, p) ->
      is_valid_id t i ->
      let (s', k) := split i (t, p) in
      i <> j ->
      k <> j ->
      get_compressed_data j (t, p) = o ->
      get_compressed_data j s' = o.
  Admitted.

  (* delete : preconds -> not is valid id on new tree, get on all other ids unchanged. *)

  (* the output of delete is valid, and the id of the delete leaf is invalid on that tree *)
  Lemma delete_valid : forall t p id,
    is_valid_state (t, p) ->
    is_valid_id t id ->
    let s' := delete id (t, p) in
    is_valid_state s' /\ not (is_valid_id (tree s') id).
  Admitted.

  Lemma delete_correct2 : forall t p i j o,
      is_valid_state (t, p) ->
      is_valid_id t i ->
      i <> j ->
      get_compressed_data j (t, p) = o ->
      let s' := delete i (t, p) in
      get_compressed_data j s' = o.
  Admitted.

  (* TODO add to validity: define validity for CData and check for each node *)

End VT.
