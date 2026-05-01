
Require Import CData.

From Stdlib Require Import Arith Lia List Permutation.
Import ListNotations.

Module VT (Data : CDATA).
  Import Data.

  Inductive VirtualTree : Type := (* the actual tree with root, branch, node and leaf *)
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

  Fixpoint is_valid_tree_data (t: VirtualTree) (p: Data.p) : Prop :=
    match t with
    | Seed => True
    | Node d c => Data.is_valid p d /\ is_valid_tree_data c p
    | Branch l r => is_valid_tree_data l p /\ is_valid_tree_data r p
    | Leaf _ => True
    end.

  Definition is_valid_tree (t: VirtualTree) : Prop :=
    is_valid_tree_structure t /\ is_valid_tree_ids t.

  Fixpoint contains_id (t: VirtualTree) (id: nat) : bool :=
    match t with
    | Seed => false
    | Node _ c => contains_id c id
    | Branch l r => contains_id l id || contains_id r id
    | Leaf i => i =? id
    end.

  Fixpoint is_valid_id (t: VirtualTree) (id: nat) : Prop :=
    match t with
    | Seed => False
    | Node _ c => is_valid_id c id
    | Branch l r => is_valid_id l id \/ is_valid_id r id
    | Leaf i => i = id
    end.

  Lemma contains_valid_id : forall t id,
      contains_id t id = true <-> is_valid_id t id.
  Proof.
    split; induction t0; intros; simpl in *; auto.
    - congruence.
    - apply Bool.orb_prop in H.
      destruct H as [Hl | Hr].
      + left.
        auto.
      + right.
        auto.
    - apply Nat.eqb_eq in H.
      assumption.
    - apply Bool.orb_true_iff.
      destruct H as [Hl | Hr].
      + left.
        auto.
      + right.
        auto.
    - apply Nat.eqb_eq.
      assumption.
  Qed.

  Lemma not_contains_valid_id : forall t id,
      contains_id t id = false <-> ~ is_valid_id t id.
  Proof.
    split; intros.
    - intros C.
      apply contains_valid_id in C.
      congruence.
    - induction t0; simpl in *; auto.
      + apply Bool.orb_false_iff.
        split; auto.
      + apply Nat.eqb_neq.
        assumption.
  Qed.
      

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
    is_valid_tree_structure (tree s) /\
      is_valid_tree_ids (tree s) /\
      is_valid_tree_data (tree s) (param s).
  

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
    | Branch l r =>
        if (contains_id l id)
        then Branch (split_in_tree id new_id l) r
        else Branch l (split_in_tree id new_id r)
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
  Fixpoint get_compressed_data_in_tree_old (id: nat) (t: VirtualTree) (p: Data.p): triple_option Data.t :=
    match t with
    | Seed => TNone
    | Node d c =>
        match get_compressed_data_in_tree_old id c p with
        | TNone => TNone
        | TEmpty => TSome d
        | TSome v => TSome (Data.compress p d v)
        end
    | Branch l r =>
        match (get_compressed_data_in_tree_old id l p) with
        | TNone => match (get_compressed_data_in_tree_old id r p) with
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

  Fixpoint get_compressed_data_in_tree' (id: nat) (t: VirtualTree) (p: Data.p) (acc: option Data.t): option Data.t :=
    match t with
    | Seed => None
    | Node d c =>
        let acc' := match acc with
                    | Some a => Some (Data.compress p a d)
                    | None => Some d
                    end in
        get_compressed_data_in_tree' id c p acc'
    | Branch l r =>
        match (get_compressed_data_in_tree' id l p acc) with
        | Some a => Some a
        | None => get_compressed_data_in_tree' id r p acc
        end
    | Leaf i => if Nat.eqb i id
                then acc
                else None
    end.

  Definition get_compressed_data (id: nat) (s: State): option Data.t :=
    get_compressed_data_in_tree' id (tree s) (param s) None.

  Definition get_compressed_data' (id:nat) (s: State) : option Data.t :=
    match get_compressed_data_in_tree_old id (tree s) (param s) with
    | TSome v => Some v
    | _ => None
    end.

  Definition is_empty_tree (t: VirtualTree) : bool :=
    match t with
    | Seed => true
    | _ => false
    end.

  Lemma greater_than_max_is_invalid_id : forall t x,
      x > max_id_in_tree t ->
      ~ is_valid_id t x.
  Proof.
    unfold not.
    intros t. induction t; intros x H C; simpl in *.
    - auto.
    - eapply IHt; eauto.
    - apply Nat.max_lub_lt_iff in H. destruct H as [H1 H2].
      destruct C as [C1 | C2];
        [apply IHt1 with (x:=x) | apply IHt2 with (x:=x)];
        auto;
        lia.
    - lia.
  Qed.

  Lemma valid_id_is_leq_max: forall t x,
      is_valid_id t x ->
      x <= max_id_in_tree t.
  Proof.
    intros t. induction t; intros x H; simpl in *.
    - lia.
    - auto.
    - destruct H as [H1 | H2].
      + apply IHt1 in H1.
        lia.
      + apply IHt2 in H2.
        lia.
    - lia.
  Qed.

  Lemma is_Leaf_with_id : forall t id,
      is_leaf_with_id t id = true -> t = Leaf id.
  Proof.
    intros t. destruct t; intros i H; simpl in *; try congruence.
    apply Nat.eqb_eq in H.
    congruence.
  Qed.    

  (* Keep seed (for now), remove counter *)
  (* Proving todo *)

  (* Insert : insert seed -> seed
    is_valid_state and is_valid input id, get on id = compress (get id oldtree, new data) /\ get on i not id = same as before, is_valid new tree *)

  Lemma insert_ids : forall t p id d,
      get_all_ids t = get_all_ids (insert_in_tree id d t p).
  Proof.
    intros t. induction t; intros param i d; simpl in *; try auto.
    - destruct (is_leaf_with_id t0 i); simpl in *; auto.
    - destruct (is_leaf_with_id t1 i); simpl in *; auto.
      destruct (is_leaf_with_id t2 i); simpl in *; auto.
      rewrite <- IHt1. rewrite <- IHt2.
      reflexivity.
  Qed.

  Lemma insert_valid_ids : forall t p id d,
      is_valid_tree_ids t ->
      is_valid_tree_ids (insert_in_tree id d t p).
  Proof.
    intros.
    unfold is_valid_tree_ids in *.
    rewrite <- insert_ids.
    assumption.
  Qed.

  Lemma insert_valid_data : forall t p id d,
      Data.is_valid p d ->
      is_valid_tree_data t p ->
      is_valid_tree_data (insert_in_tree id d t p) p.
  Proof.
    intros t. induction t; intros param i d Hd H; simpl in *.
    - tauto.
    - destruct H as [H Hc].
      destruct (is_leaf_with_id t0 i); simpl.
      + split.
        * apply Data.compress_valid; assumption.
        * assumption.
      + split; auto.
    - destruct H as [H1 H2].
      destruct (is_leaf_with_id t1 i); simpl.
      + repeat split; assumption.
      + destruct (is_leaf_with_id t2 i); simpl.
        * repeat split; assumption.
        * split; auto.
    - tauto.
  Qed.

  Lemma insert_valid_structure : forall t p id d,
      is_valid_tree_structure t ->
      is_valid_tree_structure (insert_in_tree id d t p).
  Proof.
  Admitted.
  
  (* the output state of insert is a valid state *)
  Lemma insert_valid : forall t p id d, (*might skip the t/p thing, and just use s*)
      Data.is_valid p d ->
      is_valid_state (t, p) ->
      is_valid_id t id ->
      is_valid_state (insert id d (t, p)).
  Proof.
    intros.
    unfold is_valid_state in *.
    destruct H0 as [Hs [Hids Hd]].
    repeat split.
    - apply insert_valid_structure.
      assumption.
    - apply insert_valid_ids.
      assumption.
    - apply insert_valid_data;
        assumption.
  Qed.

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

  Lemma no_dup_two {A} : forall (x y: A),
      x <> y ->
      NoDup [x; y].
  Proof.
    intros x y H.
    constructor.
    - intros C; inversion C; subst; auto.
    - apply no_dup_one.
  Qed.

  (* split: is valid old state, is valid id -> is valid new state and is valid id and new id on new state *)
  (* get on id = get on new id *) (* get on other ids unchanged *)

  Print is_valid_state.

  Lemma split_valid_structure : forall t i i',
      is_valid_tree_structure t ->
      is_valid_tree_structure (split_in_tree i i' t).
  Admitted.

  Lemma split_ids : forall t i i',
      ~ is_valid_id t i' ->
      is_valid_id t i ->
      Permutation (i' :: (get_all_ids t)) (get_all_ids (split_in_tree i i' t)).
  Proof.
    induction t0; intros i i' H' H; simpl in *.
    - contradiction.
    - auto.
    - destruct (contains_id t0_1 i) eqn:I; simpl in *.
      + Search (Permutation (_ ++ _) _).
        Search (_ :: _ ++ _).
        rewrite app_comm_cons.
        apply Permutation_app.
        * apply IHt0_1. 
          -- tauto.
          -- apply contains_valid_id.
             assumption.
        * apply Permutation_refl.
      + Search (_ :: _ ++ _).
        econstructor.
        * eapply Permutation_middle.
        * apply Permutation_app.
          -- apply Permutation_refl.
          -- apply IHt0_2.
             ++ tauto.
             ++ rewrite not_contains_valid_id in I.
                tauto.
    - rewrite H. rewrite Nat.eqb_refl.
      simpl.
      constructor.
  Qed.

  Lemma split_valid_ids: forall t i i',
      ~ is_valid_id t i' ->
      is_valid_tree_ids t ->
      is_valid_tree_ids (split_in_tree i i' t).
  Proof.
    intros t; induction t; intros i i' Hin H; simpl in *.
    - assumption.
    - unfold is_valid_tree_ids in *; simpl in *.
      auto.
    - unfold is_valid_tree_ids in *; simpl in *.
      destruct (contains_id t1 i) eqn:I; simpl.
      + 
    - destruct (id =? i).
      unfold is_valid_tree_ids in *; simpl in *.
      + unfold not in Hin.
        destruct (i' =? id) eqn:I. 
        * apply Nat.eqb_eq in I. rewrite I in *.
          tauto.
        * apply Nat.eqb_neq in I.
          apply no_dup_two.
          auto.
      + assumption.
  Admitted.
      
  Lemma split_valid_data: forall t p i i',
      is_valid_tree_data t p ->
      is_valid_tree_data (split_in_tree i i' t) p.
  Proof.
    intros t; induction t; intros param i i' H; simpl in *.
    - tauto.
    - destruct H as [Hd Hc].
      split; auto.
    - destruct H as [H1 H2].
      split; auto.
    - destruct (id =? i); simpl; tauto.
  Qed.

  Lemma split_valid_new_id: forall t i i',
      is_valid_id t i ->
      is_valid_id (split_in_tree i i' t) i'.
  Proof.
    intros t; induction t; intros i i' H; simpl in *.
    - contradiction.
    - auto.
    - destruct H as [H1 | H2]; auto.
    - rewrite H.
      rewrite Nat.eqb_refl.
      simpl.
      right.
      reflexivity.
  Qed.

  (* the output state of split is valid, and the new id is valid on that tree *)
  Lemma split_valid : forall t p id,
      is_valid_state (t, p) ->
      is_valid_id t id ->
      let (s', j) := split id (t, p) in
      is_valid_state s' /\ is_valid_id (tree s') j.
  Proof.
    intros.
    unfold is_valid_state in *.
    destruct H as [Hs [Hids Hd]].
    repeat split.
    - apply split_valid_structure.
      assumption.
    - apply split_valid_ids.
      + simpl.
        apply greater_than_max_is_invalid_id.
        lia.
      + assumption.
    - apply split_valid_data;
        assumption.
    - apply split_valid_new_id.
      assumption.    
  Qed.

  Lemma split_get_unchanged: forall t p i i' j o,
      i' <> j ->
      let t' := split_in_tree i i' t in
      get_compressed_data_in_tree' j t' p o = get_compressed_data_in_tree' j t p o.
  Proof.
    intros t. induction t; intros param i i' j o H; simpl in *.
    - reflexivity.
    - destruct o; simpl; auto.
    - rewrite IHt1 by assumption. rewrite IHt2 by assumption.
      reflexivity.
    - destruct (id =? i) eqn:I; simpl.
      + destruct (id =? j).
        * destruct o.
          -- auto.
          -- destruct (i' =? j); reflexivity.
        * apply Nat.eqb_neq in H.
          rewrite H.
          reflexivity.
      + destruct (id =? j); auto.
  Qed.

  Lemma split_get_new_leaf: forall t p i i' o,
      ~ is_valid_id t i' ->
      let t' := split_in_tree i i' t in
      get_compressed_data_in_tree' i' t' p o = get_compressed_data_in_tree' i t p o.
  Proof.
    intros t. induction t; intros param i i' o H; simpl in *.
    - reflexivity.
    - destruct o; simpl; auto.
    - rewrite IHt1; try rewrite IHt2; auto.
    - destruct (id =? i) eqn:I; simpl.
      + destruct (id =? i'); simpl.
        * destruct o; simpl.
          -- reflexivity.
          -- rewrite Nat.eqb_refl.
             reflexivity.
        * rewrite Nat.eqb_refl.
          reflexivity.
      + apply Nat.eqb_neq in H.
        rewrite H.
        congruence.
  Qed.

  (* when splitting a leaf i, the resulting new leaves have the same compressed data as i *)
  Lemma split_get_new_leaves : forall t p i o,
      is_valid_state (t, p) ->
      is_valid_id t i ->
      get_compressed_data i (t, p) = o ->
      let (s', j) := split i (t, p) in
      get_compressed_data i s' = o /\ get_compressed_data j s' = o.
  Proof.
    intros.
    simpl.
    unfold get_compressed_data in *. simpl in *.
    split.
    - rewrite split_get_unchanged.
      + assumption.
      + apply valid_id_is_leq_max in H0.
        lia.
    - rewrite split_get_new_leaf.
      + assumption.
      + apply greater_than_max_is_invalid_id.
        lia.
  Qed.

  (* when splitting leaf i, all other leaves have unchanged data *)
  Lemma split_unchanged: forall t p i j o, (*might merge this one with the previous one *)
      is_valid_state (t, p) ->
      is_valid_id t i ->
      let (s', k) := split i (t, p) in
      i <> j ->
      k <> j ->
      get_compressed_data j (t, p) = o ->
      get_compressed_data j s' = o.
  Proof.
    simpl.
    intros.
    unfold get_compressed_data in *. simpl in *.
    rewrite split_get_unchanged.
    - assumption.
    - apply valid_id_is_leq_max in H0.
      lia.
  Qed.

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
