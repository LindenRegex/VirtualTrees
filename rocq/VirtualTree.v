
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

  Lemma valid_in_ids : forall t id,
      is_valid_id t id <-> In id (get_all_ids t).
  Proof.
    intros t0 i; induction t0; split; intros H; simpl in *; auto.
    - apply IHt0.
      assumption.
    - apply IHt0.
      auto.
    - apply in_app_iff.
      destruct H as [H1 | H2].
      + left.
        apply IHt0_1.
        auto.
      + right.
        apply IHt0_2.
        auto.
    - apply in_app_iff in H.
      destruct H as [Hl | Hr].
      + left.
        apply IHt0_1.
        auto.
      + right.
        apply IHt0_2.
        auto.
    - destruct H; auto.
      contradiction.
  Qed.

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
    | Seed => acc
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
  Lemma insert_get_some : forall t p id d c_old c_new,
      is_valid_state (t, p) ->
      is_valid_id t id ->
      get_compressed_data id (t, p) = Some c_old -> (* case where data already existed for id *)
      get_compressed_data id (insert id d (t, p)) = Some c_new /\
        c_new = Data.compress p d c_old. (* TODO check compress order*)
  Proof.
    Admitted.

  (* when inserting for i with no data, the new data for i is the inserted data *)
  Lemma insert_get_none : forall t p id d c,
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

  Lemma no_dup_remove {A} : forall l l' (a: A),
      ~ In a l ->
      ~ In a l' ->
      NoDup (l ++ l') ->
      NoDup (l ++ a :: l').
  Proof.
    induction l; intros l' b Ha Ha' H; simpl in *; auto.
    - constructor; auto.
    - apply NoDup_cons_iff in H. destruct H as [H H'].
      constructor.
      + intros C.
        rewrite in_app_iff in *.
        destruct C as [C | C].
        * tauto.
        * apply in_inv in C.
          destruct C as [C | C]; try symmetry in C; tauto.
      + apply IHl; auto.
  Qed.


  Lemma no_dup_in_app {A} : forall l l' (a: A),
      NoDup (l ++ l') ->
      In a l ->
      ~ In a l'.
  Proof.
    induction l; intros l' b H Ha; simpl.
    - inversion Ha.
    - rewrite <- app_comm_cons in H.
      apply NoDup_cons_iff in H. destruct H as [Hi H].
      apply in_inv in Ha.
      destruct Ha as [Ha | Ha].
      + rewrite Ha in *.
        rewrite in_app_iff in Hi.
        tauto.
      + apply IHl; auto.
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
      + rewrite app_comm_cons.
        apply Permutation_app.
        * apply IHt0_1. 
          -- tauto.
          -- apply contains_valid_id.
             assumption.
        * apply Permutation_refl.
      + econstructor.
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

  Lemma split_on_invalid_id: forall t i i',
      ~ is_valid_id t i ->
      t = split_in_tree i i' t.
  Proof.
    intros t i i'; induction t; intros H; simpl in *; auto.
    - rewrite <- IHt; auto.
    - destruct (contains_id t1 i).
      + rewrite <- IHt1; try tauto.
      + rewrite <- IHt2; try tauto.
    - destruct (id =? i) eqn:I.
      + apply Nat.eqb_eq in I.
        congruence.
      + reflexivity.
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
      + eapply Permutation_NoDup.
        * eapply Permutation_app_tail.
          eapply split_ids; try tauto.
          apply contains_valid_id.
          assumption.
        * rewrite <- app_comm_cons.
          apply NoDup_cons; try auto.
          rewrite in_app_iff.
          repeat rewrite <- valid_in_ids.
          tauto.
      + destruct (contains_id t2 i) eqn:I2.
        * eapply Permutation_NoDup.
          -- eapply Permutation_app_head.
             apply split_ids; try tauto.
             apply contains_valid_id.
             assumption.
          -- apply no_dup_remove;
               try rewrite <- valid_in_ids;
               tauto.
        * erewrite <- split_on_invalid_id; auto.
          apply not_contains_valid_id.
          auto.
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
  Qed.
      
  Lemma split_valid_data: forall t p i i',
      is_valid_tree_data t p ->
      is_valid_tree_data (split_in_tree i i' t) p.
  Proof.
    intros t; induction t; intros param i i' H; simpl in *.
    - tauto.
    - destruct H as [Hd Hc].
      split; auto.
    - destruct H as [H1 H2].
      destruct (contains_id t1 i);
        split;
        auto.
    - destruct (id =? i); simpl; tauto.
  Qed.

  Lemma split_valid_new_id: forall t i i',
      is_valid_id t i ->
      is_valid_id (split_in_tree i i' t) i'.
  Proof.
    intros t; induction t; intros i i' H; simpl in *.
    - contradiction.
    - auto.
    - destruct H as [H1 | H2];
        destruct (contains_id t1 i) eqn:I;
        try apply contains_valid_id in I;
        simpl; auto.
        apply not_contains_valid_id in I; contradiction.
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
    - destruct (contains_id t1 i) eqn:I; simpl;
        [rewrite IHt1 by assumption | rewrite IHt2 by assumption];
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

  Lemma get_on_invalid_id : forall t p i o,
      t <> Seed ->
      is_valid_tree_structure t ->
      ~ is_valid_id t i ->
      get_compressed_data_in_tree' i t p o = None.
  Proof.
    intros t; induction t; intros param i o Ht Hs H;
      simpl in *.
    - congruence.
    - apply IHt.
      destruct o eqn:O; simpl.
      + destruct t0; simpl; congruence.
      + destruct t0; simpl; congruence.
      + destruct t0; simpl; try contradiction.
        * assumption.
        * tauto.
      + assumption.
    - rewrite IHt1; simpl.
      + apply IHt2.
        * destruct t1, t2; simpl; try contradiction; try congruence.
        * destruct t1, t2; simpl; tauto.
        * tauto.
      + destruct t1; simpl; try contradiction; congruence.
      + destruct t1, t2; simpl; tauto.
      + tauto.
    - destruct (id =? i) eqn:I.
      + apply Nat.eqb_eq in I.
        congruence.
      + reflexivity.
  Qed.

  (* i does not need to be valid, because the tree is unchanged if it is not *)
  Lemma split_get_new_leaf: forall t p i i' o,
      ~ is_valid_id t i' ->
      is_valid_tree_ids t ->
      is_valid_tree_structure t ->
      let t' := split_in_tree i i' t in
      get_compressed_data_in_tree' i' t' p o = get_compressed_data_in_tree' i t p o.
  Proof.
    intros t. induction t; intros param i i' o H Hi Hs; simpl in *.
    - reflexivity.
    - destruct o; simpl; apply IHt; auto;
        destruct t0; try contradiction; auto.
    - destruct (contains_id t1 i) eqn:I; simpl.
      + rewrite IHt1.
        * apply contains_valid_id in I.
          repeat rewrite get_on_invalid_id with (t:=t2); auto.
          1, 4: destruct t1, t2; simpl; try contradiction; congruence.
          1, 3: destruct t1 eqn:T1, t2 eqn:T2; try contradiction; rewrite <- T2 in *; tauto.
          -- unfold is_valid_tree_ids in *. simpl in *.
             rewrite valid_in_ids in *.
             eapply no_dup_in_app; eauto.
        * apply contains_valid_id in I. auto.
        * unfold is_valid_tree_ids in *; simpl in *.
          eapply NoDup_app_remove_r; eauto.
        * destruct t1 eqn:T1, t2 eqn:T2; try contradiction; rewrite <- T2 in *; tauto.
      + rewrite IHt2.
        * repeat rewrite get_on_invalid_id with (t:=t1); simpl; auto. 
          1, 4: destruct t1; simpl; try contradiction; congruence.
          1, 3: destruct t1 eqn:T1, t2 eqn:T2; try contradiction; rewrite <- T2 in *; tauto.
          -- apply not_contains_valid_id; auto.
        * apply not_contains_valid_id in I. auto.
        * unfold is_valid_tree_ids in *; simpl in *.
          eapply NoDup_app_remove_l; eauto.
        * destruct t1 eqn:T1, t2 eqn:T2; try contradiction; rewrite <- T2 in *; tauto.
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
      get_compressed_data i (t, p) = o ->
      let (s', j) := split i (t, p) in
      get_compressed_data i s' = o /\ get_compressed_data j s' = o.
  Proof.
    intros.
    unfold is_valid_state in H.
    simpl.
    unfold get_compressed_data in *. simpl in *.
    split.
    - destruct (contains_id t0 i) eqn:I; simpl.
      + rewrite split_get_unchanged.
        * assumption.
        * apply contains_valid_id in I.
          apply valid_id_is_leq_max in I.
          lia.
      + apply not_contains_valid_id in I.
        rewrite <- split_on_invalid_id with (t:=t0); auto.
    - rewrite split_get_new_leaf.
      + assumption.
      + apply greater_than_max_is_invalid_id.
        lia.
      + tauto.
      + tauto.
  Qed.

  (* when splitting leaf i, all other leaves have unchanged data *)
  (* if i is invalid, the tree does not change and the property still holds *)
  Lemma split_unchanged: forall t p i j o, (*might merge this one with the previous one *)
      is_valid_state (t, p) ->
      let (s', k) := split i (t, p) in
      i <> j ->
      k <> j ->
      get_compressed_data j (t, p) = o ->
      get_compressed_data j s' = o.
  Proof.
    simpl.
    intros.
    unfold get_compressed_data in *. simpl in *.
    destruct (contains_id t0 i) eqn:I; simpl.
    - rewrite split_get_unchanged.
      + assumption.
      + apply contains_valid_id in I.
        apply valid_id_is_leq_max in I.
        lia.
    - apply not_contains_valid_id in I.
      rewrite <- split_on_invalid_id with (t:=t0); auto.
  Qed.

  (* delete : preconds -> not is valid id on new tree, get on all other ids unchanged. *)

  Lemma delete_ids : forall t p id,
      incl (get_all_ids (delete_in_tree id t p)) (get_all_ids t).
  Proof.
    intros t; induction t; intros param i; simpl in *.
    - apply incl_refl.
    - admit.
    - destruct (is_branch_with_id i t1); simpl.
      + apply incl_appr.
        apply incl_refl.
      + destruct (is_branch_with_id i t2); simpl.
        * apply incl_appl.
          apply incl_refl.
        * apply incl_app_app; auto.
    - destruct (id =? i); simpl.
      + apply incl_nil_l.
      + apply incl_refl.
  Admitted.

  Lemma delete_valid_ids : forall t p id,
      is_valid_tree_ids t ->
      is_valid_tree_ids (delete_in_tree id t p).
  Proof.
    intros t; induction t; intros param i H; simpl in *; auto.
    - destruct (delete_in_tree i t0 param) eqn:D; unfold is_valid_tree_ids in *; simpl in *; auto.
      + constructor.
      + (* v branch of orig tree *) admit.
      + specialize (IHt param i). rewrite D in IHt. simpl in IHt.
        apply IHt.
        assumption.
      + apply no_dup_one.
    - unfold is_valid_tree_ids in *.
      destruct (is_branch_with_id i t1); simpl in *.
      + eapply NoDup_app_remove_l; eauto.
      + destruct (is_branch_with_id i t2); simpl in *.
        * eapply NoDup_app_remove_r; eauto.
        * Search (NoDup _).
      
        
  Lemma delete_valid_data : forall t p id,
      is_valid_tree_data t p ->
      is_valid_tree_data (delete_in_tree id t p) p.
  Proof.
    intros t; induction t; intros param i H; simpl in *; auto.
    - destruct (delete_in_tree i t0 param) eqn:D; simpl in *; auto.
      + (* TODO v is a branch of original tree -> all valid data *) admit. 
      + (* TODO the only way for delete to be a branch is if it was a branch before *) admit.
      + tauto.
    - destruct (is_branch_with_id i t1).
      + tauto.
      + destruct (is_branch_with_id i t2).
        * tauto.
        * simpl.
          split; [apply IHt1 | apply IHt2]; tauto.
  Admitted.

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
