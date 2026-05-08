
Require Import CData.

From Stdlib Require Import Arith Lia List Permutation.
Import ListNotations.

Module NoDupHelpers.

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

  Lemma no_dup_app_comm {A} : forall (l l': list A),
      NoDup (l ++ l') -> NoDup (l' ++ l).
  Proof.
    induction l; intros l' H; simpl in *.
    - rewrite app_nil_r.
      assumption.
    - apply NoDup_cons_iff in H. destruct H as [Hin H].
      rewrite in_app_iff in Hin.
      apply no_dup_remove; auto.
  Qed.
  
End NoDupHelpers.

Module VT (Data : CDATA).
  Import Data.

  (* Definitions *)

  (** Inductive type *)

  Inductive VirtualTree : Type := (* the actual tree with root, branch, node and leaf *)
  | Seed
  | Node (data: Data.t) (child: VirtualTree)
  | Branch (l: VirtualTree) (r: VirtualTree)
  | Leaf (id: nat).

  (** Validity *)

  (*** Structure validity *)

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

  (*** Leaves ids validity *)

  Fixpoint get_all_ids (t: VirtualTree) : list nat :=
    match t with
    | Seed => []
    | Node d c => get_all_ids c
    | Branch l r => (get_all_ids l) ++ (get_all_ids r)
    | Leaf id => [id]
    end.

  Definition is_valid_tree_ids (t: VirtualTree) : Prop := NoDup (get_all_ids t).

  (*** Node data validity *)

  Fixpoint is_valid_tree_data (t: VirtualTree) (p: Data.p) : Prop :=
    match t with
    | Seed => True
    | Node d c => Data.is_valid p d /\ is_valid_tree_data c p
    | Branch l r => is_valid_tree_data l p /\ is_valid_tree_data r p
    | Leaf _ => True
    end.

  (*** External id validity *)

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

  Fixpoint max_id_in_tree (t: VirtualTree) : nat :=
    match t with
    | Seed => 0 (*removed the option for cleaner split *)
    | Node _ c => max_id_in_tree c
    | Branch l r => Nat.max (max_id_in_tree l) (max_id_in_tree r)
    | Leaf i => i
    end.

  (** State *)

  Definition State := (VirtualTree * Data.p)%type. (* TODO remove counter *)

  Definition tree (s: State) : VirtualTree :=
    match s with
    | (t, _) => t
    end.
  
  Definition param (s: State) : Data.p :=
    match s with
    | (_, p) => p
    end.

  Definition is_valid_state (s: State) : Prop :=
    is_valid_tree_structure (tree s) /\
      is_valid_tree_ids (tree s) /\
      is_valid_tree_data (tree s) (param s).

  (* TODO clean this up *)

  Definition empty (param: Data.p) : State :=
    (Seed, param).

  Definition with_one_leaf (param: Data.p) : State :=
    (Leaf 0, param).

  (** Boolean structure checkers *)
  
  Definition is_leaf_with_id (t: VirtualTree) (id: nat) : bool :=
    match t with
    | Leaf i => Nat.eqb i id
    | _ => false
    end.

  Definition is_seed (t: VirtualTree) : bool :=
    match t with
    | Seed => true
    | _ => false
    end.

  Fixpoint is_branch_with_id (id : nat) (t: VirtualTree) : bool :=
    match t with
    | Seed => false
    | Node _ c => is_branch_with_id id c
    | Branch _ _ => false
    | Leaf i => Nat.eqb i id
    end.

  (** Operations *)

  (*** Insert: add some data (Data.t) at one leaf *)

  Fixpoint insert_in_tree (id: nat) (new: Data.t) (t: VirtualTree) (p: Data.p) : VirtualTree :=
    match t with
    | Seed => Seed
    | Node d c => if is_leaf_with_id c id
                  then Node (Data.compress p d new) c
                  else Node d (insert_in_tree id new c p)
    | Branch l r => Branch (insert_in_tree id new l p) (insert_in_tree id new r p)
        (*if is_leaf_with_id l id
                    then Branch (Node new l) r
                    else if is_leaf_with_id r id
                         then Branch l (Node new r)
                         else Branch (insert_in_tree id new l p) (insert_in_tree id new r p)*)
    | Leaf i => if (i =? id)
                then Node new (Leaf i)
                else Leaf i
    end.

  Definition insert (id: nat) (new : Data.t) (s: State) : State :=
    (insert_in_tree id new (tree s) (param s), param s).

  (*** Split: replace a leaf with a branch with two leaves children *)

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

  (*** Delete: delete a leaf *)

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

  (*** Get: get the compressed data for one leaf *)

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

  (* Properties *)

  (** Id validity helpers *)

  Lemma valid_in_ids : forall t id,
      is_valid_id t id <-> In id (get_all_ids t).
  Proof.
    intros t i; induction t;
      split; intros H;
      simpl in *;
      try apply IHt; auto.
    - apply in_app_iff.
      destruct H as [H1 | H2];
        [left | right];
        [apply IHt1 | apply IHt2];
        auto.
    - apply in_app_iff in H.
      destruct H as [Hl | Hr];
        [left | right];
        [apply IHt1 | apply IHt2];
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
      destruct H as [Hl | Hr];
        [left | right]; auto.
    - apply Nat.eqb_eq in H.
      assumption.
    - apply Bool.orb_true_iff.
      destruct H as [Hl | Hr];
        [left | right]; auto.
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
    intros t. induction t; intros x H; simpl in *;
      auto; try lia.
    - destruct H as [H1 | H2].
      + apply IHt1 in H1.
        lia.
      + apply IHt2 in H2.
        lia.
  Qed.

  Lemma valid_id_branch_xor : forall l r id,
      is_valid_tree_ids (Branch l r) ->
      is_valid_id (Branch l r) id ->
      ~ (is_valid_id l id ) \/ ~ (is_valid_id r id).
  Proof.
    intros l r id H Hi.
    unfold is_valid_tree_ids in H. simpl in H.
    apply contains_valid_id in Hi. simpl in Hi.
    apply Bool.orb_prop in Hi.
    destruct Hi as [Hi | Hi];
      [right | left];
      apply contains_valid_id in Hi;
      rewrite valid_in_ids in *;
      eapply NoDupHelpers.no_dup_in_app; eauto.
    apply NoDupHelpers.no_dup_app_comm; auto.
  Qed.

  Lemma valid_ids_branch : forall l r,
      is_valid_tree_ids (Branch l r) ->
      is_valid_tree_ids l /\ is_valid_tree_ids r.
  Proof.
    intros l r H.
    unfold is_valid_tree_ids in *.
    simpl in *.
    split;
      [eapply NoDup_app_remove_r | eapply NoDup_app_remove_l];
      eauto.
  Qed.

  (** Structure helpers *)

  Lemma is_Leaf_with_id : forall t id,
      is_leaf_with_id t id = true -> t = Leaf id.
  Proof.
    intros t i H. destruct t; simpl in *; try congruence.
    apply Nat.eqb_eq in H.
    congruence.
  Qed.

  Lemma is_Seed : forall t,
      is_seed t = true -> t = Seed.
  Proof.
    intros t H; destruct t; simpl in *; try congruence.
  Qed.

  Lemma is_not_Seed : forall t,
      is_seed t = false -> t <> Seed.
  Proof.
    intros t H; destruct t; simpl in *; congruence.
  Qed.

  Lemma node_of_child_with_valid_structure : forall d c,
      c <> Seed ->
      (forall d' c', c <> Node d' c') ->
      is_valid_tree_structure c ->
      is_valid_tree_structure (Node d c).
  Proof.
    intros. simpl in *.
    destruct c; auto.
    specialize (H0 data c).
    congruence.
  Qed.

  Lemma branch_of_children_with_valid_structure : forall l r,
      l <> Seed ->
      r <> Seed ->
      is_valid_tree_structure l ->
      is_valid_tree_structure r ->
      is_valid_tree_structure (Branch l r).
  Proof.
    intros. simpl in *.
    destruct l; destruct r; auto.
  Qed.

  Lemma branch_children_valid_struct : forall l r,
      is_valid_tree_structure (Branch l r) ->
      is_valid_tree_structure l /\ is_valid_tree_structure r.
  Proof.
    intros l r H; simpl in *; destruct l, r; try contradiction; tauto.
  Qed.

  Lemma branch_no_seed_children : forall l r,
      is_valid_tree_structure (Branch l r) ->
      l <> Seed /\ r <> Seed.
  Proof.
    intros l r H; simpl in *; split; destruct _; try contradiction; destruct _; try congruence.
  Qed.

  (** Get helpers *)

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
        * apply branch_no_seed_children in Hs. tauto.
        * apply branch_children_valid_struct in Hs. tauto.
        * tauto.
      + apply branch_no_seed_children in Hs. tauto.
      + apply branch_children_valid_struct in Hs. tauto.
      + tauto.
    - destruct (id =? i) eqn:I.
      + apply Nat.eqb_eq in I.
        congruence.
      + reflexivity.
  Qed.

  Lemma contains_get_from_some : forall t p i d,
      is_valid_tree_structure t ->
      is_valid_tree_ids t ->
      is_valid_id t i ->
      (exists d', get_compressed_data_in_tree' i t p (Some d) = Some d').
  Proof.
    intros t. induction t; intros param i d Hs Hids Hi; simpl in *; eauto.
    - eapply IHt; eauto.
      destruct t0; try contradiction; congruence.
    - pose proof valid_id_branch_xor as XOR.
      specialize (XOR t1 t2 i Hids Hi).
      destruct Hi as [Hi | Hi].
      + eapply IHt1 in Hi. destruct Hi as [d' Hi].
        erewrite Hi.
        * eauto.
        * apply branch_children_valid_struct in Hs. tauto.
        * apply valid_ids_branch in Hids. tauto.
      + rewrite get_on_invalid_id.
        * eapply IHt2; try tauto.
          -- apply branch_children_valid_struct in Hs. tauto.
          -- apply valid_ids_branch in Hids. tauto.
        * apply branch_no_seed_children in Hs. tauto.
        * apply branch_children_valid_struct in Hs. tauto.
        * tauto.
    - subst.
      rewrite Nat.eqb_refl.
      eauto.
  Qed.

  (** Insert properties *)

  (*** Insert: Validity of resulting state *)

  Lemma insert_ids : forall t p id d,
      get_all_ids t = get_all_ids (insert_in_tree id d t p).
  Proof.
    intros t. induction t; intros param i d; simpl in *; try auto.
    - destruct (is_leaf_with_id t0 i); simpl in *; auto.
    - rewrite <- IHt1. rewrite <- IHt2; auto.
    - destruct (id =? i) eqn:I; simpl; auto.
  Qed.

  Lemma insert_valid_ids : forall t p id d,
      is_valid_tree_ids t ->
      is_valid_tree_ids (insert_in_tree id d t p).
  Proof.
    intros.
    unfold is_valid_tree_ids in *.
    rewrite <- insert_ids;
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
      split; auto.
    - destruct (id =? i); simpl; tauto.
  Qed.

  Lemma insert_is_seed : forall t p id d,
      insert_in_tree id d t p = Seed -> t = Seed.
  Proof.
    intros t p id d H.
    destruct t; simpl in *; try congruence.
    - destruct (is_leaf_with_id _); simpl; congruence.
    - destruct (_ =? _); congruence.
  Qed.

  Lemma insert_is_not_seed : forall t p id d,
      t <> Seed -> (insert_in_tree id d t p) <> Seed.
  Proof.
    intros t. intros.
    destruct t; simpl in *; try congruence.
    - destruct (is_leaf_with_id _ _); congruence.
    - destruct (_ =? _); congruence.
  Qed.

  Lemma insert_valid_structure : forall t p id d,
      is_valid_tree_structure t ->
      is_valid_tree_structure (insert_in_tree id d t p).
  Proof.
    intros t; induction t; intros param i d H; auto.
    - simpl in *.
      destruct t0 eqn:T0; try contradiction.
      + unfold is_leaf_with_id.
        apply node_of_child_with_valid_structure;
          auto;
          try intros; simpl;
          congruence.
      + simpl in *.
        destruct (id =? i); auto.
    - simpl insert_in_tree.
      simpl in H.
      apply branch_of_children_with_valid_structure.
      + destruct (is_seed t1) eqn:T1.
        * apply is_Seed in T1. rewrite T1 in *.
          contradiction.
        * apply insert_is_not_seed.
          apply is_not_Seed.
          assumption.
      + destruct (is_seed t2) eqn:T2.
        * apply is_Seed in T2. rewrite T2 in *.
          destruct t1; contradiction.
        * apply insert_is_not_seed.
          apply is_not_Seed.
          assumption.
      + apply IHt1. apply branch_children_valid_struct in H. tauto.
      + apply IHt2. apply branch_children_valid_struct in H. tauto.
    - simpl in *.
      destruct (id =? i); auto.
  Qed.
  
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

  (*** Insert: Get on resulting state *)

  Lemma insert_on_invalid_id : forall t p i d,
      ~ is_valid_id t i ->
      t = insert_in_tree i d t p.
  Proof.
    intros t p i d. induction t; intros H; simpl in *; auto.
    - destruct (is_leaf_with_id t0 i) eqn:L.
      + apply is_Leaf_with_id in L. subst.
        simpl in *.
        congruence.
      + rewrite <- IHt; auto.
    - rewrite <- IHt1, <- IHt2; auto.
    - apply Nat.eqb_neq in H.
      rewrite H.
      reflexivity.
  Qed.

  Lemma insert_get_none_in_tree : forall t p id d o,
      is_valid_tree_structure t ->
      is_valid_tree_ids t ->
      is_valid_id t id -> (* needed*)
      get_compressed_data_in_tree' id t p o = None ->
      get_compressed_data_in_tree' id (insert_in_tree id d t p) p o = Some d.
  Proof.
    intros t; induction t;
      intros param i d o Hs Hids Hid H;
      simpl in *.
    - contradiction.
    - apply contains_get_from_some with
        (d:= match o with | Some a => compress param a data | None => data end)
        (p:= param)
        in Hid.
      + destruct Hid as [d' Hid].
        destruct o; try congruence.
      + destruct t0; try contradiction; auto.
      + unfold is_valid_tree_ids in *; auto.
    - pose proof valid_id_branch_xor as XOR.
      specialize (XOR t1 t2 i Hids Hid).
      destruct Hid as [H1 | H2].
      + destruct (get_compressed_data_in_tree' i t1 param o) eqn:G; try congruence.
        erewrite IHt1; eauto.
        * apply branch_children_valid_struct in Hs. tauto.
        * apply valid_ids_branch in Hids. tauto.
      + rewrite get_on_invalid_id.
        * apply IHt2; eauto.
          -- apply branch_children_valid_struct in Hs. tauto.
          -- apply valid_ids_branch in Hids. tauto.
          -- destruct (get_compressed_data_in_tree' i t1 param o);
               try congruence; auto.
        * apply insert_is_not_seed. destruct t1; try contradiction; congruence.
        * destruct t1, t2; try contradiction; apply insert_valid_structure; tauto.
        * rewrite <- insert_on_invalid_id; tauto.
    - subst.
      rewrite Nat.eqb_refl in *; simpl.
      rewrite Nat.eqb_refl. subst.
      reflexivity.
  Qed.

  Lemma insert_get_none : forall t p id d,
      is_valid_state (t, p) ->
      is_valid_id t id ->
      get_compressed_data id (t, p) = None ->
      get_compressed_data id (insert id d (t, p)) = Some d.
  Proof.
    intros t param id d [Hs [Hids Hd]] Hid H.
    unfold get_compressed_data.
    unfold insert.
    simpl.
    apply insert_get_none_in_tree; auto.
  Qed.

  Lemma invalid_id_in_insert : forall t p i d id,
      ~ is_valid_id t id ->
      ~ is_valid_id (insert_in_tree i d t p) id.
  Proof.
    intros.
    rewrite valid_in_ids in *.
    rewrite <- insert_ids in *.
    assumption.
  Qed.

  Lemma insert_get_some_in_tree : forall t p id d c_old o,
      is_valid_tree_structure t ->
      is_valid_tree_ids t ->
      is_valid_id t id ->
      get_compressed_data_in_tree' id t p o = Some c_old -> (* case where data already existed for id *)
      get_compressed_data_in_tree' id (insert_in_tree id d t p) p o = Some (Data.compress p c_old d).
  Proof.
    intros t; induction t; intros param i d c_old o Hs Hids Hi H; simpl in *; auto.
    - contradiction.
    - destruct (is_leaf_with_id t0 i) eqn:L.
      + apply is_Leaf_with_id in L. subst. simpl in *.
        rewrite Nat.eqb_refl in *.
        destruct o. 
        * injection H as H. subst.
          rewrite Data.compress_assoc.
          reflexivity.
        * injection H as H. subst.
          reflexivity.
      + simpl.
        destruct o;
          apply IHt; auto;
          destruct t0; try contradiction; auto.
    - pose proof valid_id_branch_xor as XOR.
      specialize (XOR t1 t2 i Hids Hi).
      destruct Hi as [Hi | Hi].
      + destruct (get_compressed_data_in_tree' i t1 param o) eqn:G.
        * injection H as H.
          rewrite IHt1 with (c_old := t0); auto; try congruence.
          -- apply branch_children_valid_struct in Hs. tauto.
          -- apply valid_ids_branch in Hids; tauto.
        * rewrite get_on_invalid_id with (t:=t2) in H; try congruence; try tauto.
          -- apply branch_no_seed_children in Hs. tauto.
          -- apply branch_children_valid_struct in Hs. tauto.
      + rewrite get_on_invalid_id with (t:=t1) in H; try tauto.
        -- rewrite get_on_invalid_id.
           ++ apply IHt2; auto; try congruence.
              ** apply branch_children_valid_struct in Hs. tauto.
              ** apply valid_ids_branch in Hids. tauto.
           ++ apply insert_is_not_seed.
              apply branch_no_seed_children in Hs. tauto.
           ++ apply insert_valid_structure.
              apply branch_children_valid_struct in Hs. tauto.
           ++ apply invalid_id_in_insert.
              tauto.
        -- apply branch_no_seed_children in Hs. tauto.
        -- apply branch_children_valid_struct in Hs. tauto.
    - apply Nat.eqb_eq in Hi. rewrite Hi in *.
      simpl. rewrite Hi.
      subst.
      reflexivity.
  Qed.

  Lemma insert_get_some : forall t p id d c_old,
      is_valid_state (t, p) ->
      is_valid_id t id ->
      get_compressed_data id (t, p) = Some c_old -> (* case where data already existed for id *)
      get_compressed_data id (insert id d (t, p)) = Some (Data.compress p c_old d).
  Proof.
    intros t p id d c [Hs [Hids Hd]] Hid H.
    unfold get_compressed_data.
    unfold insert.
    apply insert_get_some_in_tree; auto.
  Qed.

  Lemma insert_get_unchanged : forall t p i j d o o',
      i <> j ->
      get_compressed_data_in_tree' j t p o' = o ->
      get_compressed_data_in_tree' j (insert_in_tree i d t p) p o' = o.
  Proof.
    intros t; induction t;
      intros param i j d o o' Hij H;
      simpl in *.
    - assumption.
    - destruct (is_leaf_with_id t0 i) eqn:L; simpl.
      + apply is_Leaf_with_id in L. subst. simpl.
        apply Nat.eqb_neq in Hij.
        rewrite Hij.
        reflexivity.
      + rewrite IHt with (o:= o); auto.
    - destruct (get_compressed_data_in_tree' j t1 param o') eqn:G.
      + rewrite IHt1 with (o := Some t0); auto.
      + rewrite IHt1 with (o := None); auto.
    - destruct (id =? i) eqn:I; simpl.
      + apply Nat.eqb_eq in I. subst.
        apply Nat.eqb_neq in Hij. rewrite Hij.
        reflexivity.
      + assumption.
  Qed.

  (* the data for all other leaves is unchanged *)
  Lemma insert_unchanged : forall t p i j d o,
      i <> j ->
      get_compressed_data j (t, p) = o ->
      get_compressed_data j (insert i d (t, p)) = o.
  Proof.
    intros t param i j d o Hij H.
    unfold get_compressed_data in *.
    apply insert_get_unchanged; auto.
  Qed.

  (** Split properties *)

  (*** Split structure helpers *)

  Lemma split_is_seed : forall t i i',
      split_in_tree i i' t = Seed -> t = Seed.
  Proof.
    intros t i i' H.
    destruct t; simpl in *; auto; try congruence.
    - destruct (contains_id t1 i); congruence.
    - destruct (id =? i); congruence.
  Qed.

  Lemma split_is_node : forall t i i' d c,
      split_in_tree i i' t = Node d c ->
      (exists c', t = Node d c' /\ c = split_in_tree i i' c').
  Proof.
    intros t i i' d c H.
    destruct t; simpl in *; try congruence.
    - exists t0.
      injection H as Hd Hc. subst.
      auto.
    - destruct (contains_id t1 i); simpl; try congruence.
    - destruct (id =? i); simpl; congruence.
  Qed.

  Lemma split_is_branch : forall t i i' l r,
      split_in_tree i i' t = Branch l r ->
      (exists l', t = Branch l' r /\ l = split_in_tree i i' l') \/
        (exists r', t = Branch l r' /\ r = split_in_tree i i' r') \/
        (t = Leaf i /\ l = Leaf i /\ r = Leaf i').
  Proof.
    intros t i i' l r H.
    destruct t; simpl in *; try congruence.
    - destruct (contains_id t1 i).
      + left.
        exists t1.
        injection H as H1 H2. subst.
        auto.
      + right. left.
        exists t2.
        injection H as H1 H2. subst.
        auto.
    - right. right.
      destruct (id =? i) eqn:I; try congruence.
      injection H as Hl Hr. subst.
      apply Nat.eqb_eq in I. subst.
      auto.
  Qed.

  Lemma split_is_leaf : forall t i i' id,
      split_in_tree i i' t = Leaf id ->
      t = Leaf id.
  Proof.
    intros t i i' id H.
    destruct t; simpl in *; try congruence.
    - destruct (contains_id t1 i); simpl; try congruence.
    - destruct (id0 =? i); simpl; try congruence.
  Qed.

  (*** Split: Validity of resulting state *)

  Lemma split_valid_structure : forall t i i',
      is_valid_tree_structure t ->
      is_valid_tree_structure (split_in_tree i i' t).
  Proof.
    intros t. induction t; intros i i' H; simpl in *.
    - tauto.
    - destruct (split_in_tree i i' t0) eqn:S; simpl.
      + apply split_is_seed in S.
        rewrite S in H.
        contradiction.
      + apply split_is_node in S.
        destruct S as [d' [S _]]. rewrite S in H.
        contradiction.
      + destruct t0; try contradiction.
        * apply IHt with (i:=i) (i':=i') in H.
          rewrite S in H. simpl in H.
          assumption.
        * simpl in S.
          destruct (id =? i); simpl in S.
          -- injection S as S1 S2. subst.
             simpl. tauto.
          -- congruence.
      + tauto.
    - destruct (contains_id t1 i) eqn:C.
      + simpl.
        destruct (split_in_tree i i' t1) eqn:S.
        * apply split_is_seed in S.
          rewrite S in H.
          contradiction.
        * apply split_is_node in S. 
          destruct S as [d' [S S']]. rewrite S in H.
          rewrite S'.
          destruct t2; try contradiction; destruct H as [H1 H2]; split; auto.
          -- simpl in H1.
             simpl.
             destruct (split_in_tree i i' d') eqn:AAA.
             ++ admit.
             ++ admit.
             ++ admit.
             ++ simpl. tauto.
          -- simpl in H1.
             simpl.
             destruct (split_in_tree i i' d') eqn:AAA.
             ++ admit.
             ++ admit.
             ++ admit.
             ++ simpl. tauto.
          -- simpl in H1.
             simpl.
             destruct (split_in_tree i i' d') eqn:AAA.
             ++ admit.
             ++ admit.
             ++ admit.
             ++ simpl. tauto.
        * destruct t1; destruct t2; try contradiction; destruct H as [H H']; split; auto.
          all: try simpl in S; try congruence.
          1, 2, 3: admit.
          1, 2, 3: destruct (id =? i); try congruence;
          try injection S as S1 S2; subst; simpl; tauto.
        * apply split_is_leaf in S. rewrite S in H.
          assumption.
      + simpl.
        destruct t1; try contradiction.
        * destruct (split_in_tree i i' t2) eqn:S.
          -- admit.
          -- admit.
          -- apply split_is_branch in S. destruct S as [[l' [r' S]] | [St [Sl Sr]]].
             ++ rewrite S in H.
                admit.
             ++ subst.
                split; try tauto.
                simpl. tauto.
          -- apply split_is_leaf in S. subst.
             assumption.
        * destruct (split_in_tree i i' t2) eqn:S.
          -- admit.
          -- admit.
          -- apply split_is_branch in S. destruct S as [[l' [r' S]] | [St [Sl Sr]]].
             ++ rewrite S in H.
                admit.
             ++ subst.
                split; try tauto.
                simpl. tauto.
          -- apply split_is_leaf in S. subst.
             assumption.
        * destruct (split_in_tree i i' t2) eqn:S.
          -- admit.
          -- admit.
          -- apply split_is_branch in S. destruct S as [[l' [r' S]] | [St [Sl Sr]]].
             ++ rewrite S in H.
                admit.
             ++ subst.
                split; try tauto.
                simpl. tauto.
          -- apply split_is_leaf in S. subst.
             assumption.
    - destruct (id =? i); simpl; auto.
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
  Admitted.
      
        
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
