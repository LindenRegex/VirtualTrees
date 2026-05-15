
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
  | Stump
  | Node (data: Data.t) (child: VirtualTree)
  | Branch (l: VirtualTree) (r: VirtualTree)
  | Leaf (id: nat).

  (** Validity *)

  (*** Structure validity *)

  Fixpoint is_valid_tree_structure (t: VirtualTree) : Prop :=
    match t with
    | Stump => True
    | Node _ c => match c with
                  | Stump => False
                  | Node _ _ => False
                  | _ => is_valid_tree_structure c
                  end
    | Branch l r => match l, r with
                    | Stump, _ => False
                    | _, Stump => False
                    | _, _ => (is_valid_tree_structure l) /\ (is_valid_tree_structure r)
                    end
    | Leaf _ => True
    end.

  (*** Leaves ids validity *)

  Fixpoint get_all_ids (t: VirtualTree) : list nat :=
    match t with
    | Stump => []
    | Node d c => get_all_ids c
    | Branch l r => (get_all_ids l) ++ (get_all_ids r)
    | Leaf id => [id]
    end.

  Definition is_valid_tree_ids (t: VirtualTree) : Prop := NoDup (get_all_ids t).

  (*** Node data validity *)

  Fixpoint is_valid_tree_data (t: VirtualTree) (p: Data.p) : Prop :=
    match t with
    | Stump => True
    | Node d c => Data.is_valid p d /\ is_valid_tree_data c p
    | Branch l r => is_valid_tree_data l p /\ is_valid_tree_data r p
    | Leaf _ => True
    end.

  (*** External id validity *)

  Fixpoint contains_id (t: VirtualTree) (id: nat) : bool :=
    match t with
    | Stump => false
    | Node _ c => contains_id c id
    | Branch l r => contains_id l id || contains_id r id
    | Leaf i => i =? id
    end.

  Fixpoint is_valid_id (t: VirtualTree) (id: nat) : Prop :=
    match t with
    | Stump => False
    | Node _ c => is_valid_id c id
    | Branch l r => is_valid_id l id \/ is_valid_id r id
    | Leaf i => i = id
    end.

  Fixpoint max_id_in_tree (t: VirtualTree) : nat :=
    match t with
    | Stump => 0 (*removed the option for cleaner split *)
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
    (Stump, param).

  Definition with_one_leaf (param: Data.p) : State :=
    (Leaf 0, param).

  (** Boolean structure checkers *)
  
  Definition is_leaf_with_id (t: VirtualTree) (id: nat) : bool :=
    match t with
    | Leaf i => Nat.eqb i id
    | _ => false
    end.

  Definition is_stump (t: VirtualTree) : bool :=
    match t with
    | Stump => true
    | _ => false
    end.

  Fixpoint is_branch_with_id (id : nat) (t: VirtualTree) : bool :=
    match t with
    | Stump => false
    | Node _ c => is_branch_with_id id c
    | Branch _ _ => false
    | Leaf i => Nat.eqb i id
    end.

  (** Operations *)

  (*** Insert: add some data (Data.t) at one leaf *)

  Fixpoint insert_in_tree (id: nat) (new: Data.t) (t: VirtualTree) (p: Data.p) : VirtualTree :=
    match t with
    | Stump => Stump
    | Node d c => if is_leaf_with_id c id
                  then Node (Data.compress p d new) c
                  else Node d (insert_in_tree id new c p)
    | Branch l r => Branch (insert_in_tree id new l p) (insert_in_tree id new r p)
    | Leaf i => if (i =? id)
                then Node new (Leaf i)
                else Leaf i
    end.

  Definition insert (id: nat) (new : Data.t) (s: State) : State :=
    (insert_in_tree id new (tree s) (param s), param s).

  (*** Split: replace a leaf with a branch with two leaves children *)

  Fixpoint split_in_tree (id: nat) (new_id: nat) (t: VirtualTree) : VirtualTree :=
    match t with
    | Stump => Stump
    | Node d c => Node d (split_in_tree id new_id c)
    | Branch l r => Branch (split_in_tree id new_id l) (split_in_tree id new_id r)
        (*if (contains_id l id)
        then Branch (split_in_tree id new_id l) r
        else Branch l (split_in_tree id new_id r)*)
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
    | Stump => Stump
    | Node d c =>
        let c' := delete_in_tree id c p in
        match c' with
        | Stump => Stump
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
                then Stump
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
    | Stump => TNone
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
    | Stump => acc
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

  Lemma is_Stump : forall t,
      is_stump t = true -> t = Stump.
  Proof.
    intros t H; destruct t; simpl in *; try congruence.
  Qed.

  Lemma is_not_Stump : forall t,
      is_stump t = false -> t <> Stump.
  Proof.
    intros t H; destruct t; simpl in *; congruence.
  Qed.

  Lemma node_of_child_with_valid_structure : forall d c,
      c <> Stump ->
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
      l <> Stump ->
      r <> Stump ->
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

  Lemma branch_no_Stump_children : forall l r,
      is_valid_tree_structure (Branch l r) ->
      l <> Stump /\ r <> Stump.
  Proof.
    intros l r H; simpl in *; split; destruct _; try contradiction; destruct _; try congruence.
  Qed.

  Lemma is_branch_with_id_struct : forall t id,
      is_valid_tree_structure t ->
      is_branch_with_id id t = true ->
      (t = Leaf id \/ (exists d, t = Node d (Leaf id))).
  Proof.
    intros t id; induction t; intros Hs H; simpl in *; try congruence.
    - right.
      destruct t0 eqn:T0; try contradiction; simpl in *; try congruence.
      exists data.
      apply Nat.eqb_eq in H.
      congruence.
    - left.
      apply Nat.eqb_eq in H.
      congruence.
  Qed.

  (** Get helpers *)

  Lemma get_on_invalid_id : forall t p i o,
      t <> Stump ->
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
        * apply branch_no_Stump_children in Hs. tauto.
        * apply branch_children_valid_struct in Hs. tauto.
        * tauto.
      + apply branch_no_Stump_children in Hs. tauto.
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
        * apply branch_no_Stump_children in Hs. tauto.
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

  Lemma insert_is_Stump : forall t p id d,
      insert_in_tree id d t p = Stump -> t = Stump.
  Proof.
    intros t p id d H.
    destruct t; simpl in *; try congruence.
    - destruct (is_leaf_with_id _); simpl; congruence.
    - destruct (_ =? _); congruence.
  Qed.

  Lemma insert_is_not_Stump : forall t p id d,
      t <> Stump -> (insert_in_tree id d t p) <> Stump.
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
      + destruct (is_stump t1) eqn:T1.
        * apply is_Stump in T1. rewrite T1 in *.
          contradiction.
        * apply insert_is_not_Stump.
          apply is_not_Stump.
          assumption.
      + destruct (is_stump t2) eqn:T2.
        * apply is_Stump in T2. rewrite T2 in *.
          destruct t1; contradiction.
        * apply insert_is_not_Stump.
          apply is_not_Stump.
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
        * apply insert_is_not_Stump. destruct t1; try contradiction; congruence.
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
      is_valid_tree_data t p ->
      is_valid_id t id ->
      Data.is_valid p d ->
      (forall o', o = Some o' -> Data.is_valid p o') -> 
      get_compressed_data_in_tree' id t p o = Some c_old -> (* case where data already existed for id *)
      get_compressed_data_in_tree' id (insert_in_tree id d t p) p o = Some (Data.compress p c_old d).
  Proof.
    intros t; induction t; intros param i d c_old o Hs Hids Hdata Hi Hd Ho H; simpl in *; auto.
    - contradiction.
    - destruct (is_leaf_with_id t0 i) eqn:L.
      + apply is_Leaf_with_id in L. subst. simpl in *.
        rewrite Nat.eqb_refl in *.
        destruct o eqn:O.
        * injection H as H. rewrite <- H.
          rewrite Data.compress_assoc; auto.
          tauto.
        * injection H as H. subst.
          reflexivity.
      + simpl.
        destruct o eqn:O;
          apply IHt; auto;
          destruct t0 eqn:T0; try contradiction; auto; try tauto;
          intros o' H'; injection H' as H'; rewrite <- H';
          try apply Data.compress_valid;
          try tauto; apply Ho; auto.
    - pose proof valid_id_branch_xor as XOR.
      specialize (XOR t1 t2 i Hids Hi).
      destruct Hi as [Hi | Hi].
      + destruct (get_compressed_data_in_tree' i t1 param o) eqn:G.
        * injection H as H.
          rewrite IHt1 with (c_old := t0); auto; try congruence.
          -- apply branch_children_valid_struct in Hs. tauto.
          -- apply valid_ids_branch in Hids; tauto.
          -- tauto.
        * rewrite get_on_invalid_id with (t:=t2) in H; try congruence; try tauto.
          -- apply branch_no_Stump_children in Hs. tauto.
          -- apply branch_children_valid_struct in Hs. tauto.
      + rewrite get_on_invalid_id with (t:=t1) in H; try tauto.
        -- rewrite get_on_invalid_id.
           ++ apply IHt2; auto; try congruence.
              ** apply branch_children_valid_struct in Hs. tauto.
              ** apply valid_ids_branch in Hids. tauto.
              ** tauto.
           ++ apply insert_is_not_Stump.
              apply branch_no_Stump_children in Hs. tauto.
           ++ apply insert_valid_structure.
              apply branch_children_valid_struct in Hs. tauto.
           ++ apply invalid_id_in_insert.
              tauto.
        -- apply branch_no_Stump_children in Hs. tauto.
        -- apply branch_children_valid_struct in Hs. tauto.
    - apply Nat.eqb_eq in Hi. rewrite Hi in *.
      simpl. rewrite Hi.
      subst.
      reflexivity.
  Qed.

  Lemma insert_get_some : forall t p id d c_old,
      is_valid_state (t, p) ->
      is_valid_id t id ->
      Data.is_valid p d ->
      get_compressed_data id (t, p) = Some c_old -> (* case where data already existed for id *)
      get_compressed_data id (insert id d (t, p)) = Some (Data.compress p c_old d).
  Proof.
    intros t p id d c [Hs [Hids Hd]] Hid H.
    unfold get_compressed_data.
    unfold insert.
    apply insert_get_some_in_tree; auto.
    intros. congruence.
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

  Lemma split_on_invalid_id: forall t i i',
      ~ is_valid_id t i ->
      t = split_in_tree i i' t.
  Proof.
    intros t i i'; induction t; intros H; simpl in *; auto.
    - rewrite <- IHt; auto.
    - destruct (contains_id t1 i);
        rewrite <- IHt1; try tauto;
        rewrite <- IHt2; try tauto.
    - destruct (id =? i) eqn:I.
      + apply Nat.eqb_eq in I.
        congruence.
      + reflexivity.
  Qed.

  (*** Split structure helpers *)

  Lemma split_is_Stump : forall t i i',
      split_in_tree i i' t = Stump -> t = Stump.
  Proof.
    intros t i i' H.
    destruct t; simpl in *; auto; try congruence.
    (*- destruct (contains_id t1 i); congruence.*)
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
    (*- destruct (contains_id t1 i); simpl; try congruence.*)
    - destruct (id =? i); simpl; congruence.
  Qed.

  Lemma split_is_branch : forall t i i' l r,
      is_valid_tree_ids t ->
      split_in_tree i i' t = Branch l r ->
      (exists l', t = Branch l' r /\ l = split_in_tree i i' l') \/
        (exists r', t = Branch l r' /\ r = split_in_tree i i' r') \/
        (t = Leaf i /\ l = Leaf i /\ r = Leaf i').
  Proof.
    intros t i i' l r Hids H.
    destruct t; simpl in *; try congruence.
    - pose proof valid_id_branch_xor as XOR.
      destruct (contains_id t1 i) eqn:I1.
      + left.
        assert (I': contains_id (Branch t1 t2) i = true) by
          (simpl; rewrite I1; apply Bool.orb_true_l).
        apply contains_valid_id in I1, I'.
        specialize (XOR t1 t2 i Hids I').
        exists t1.
        rewrite <- split_on_invalid_id with (t:=t2) in H.
        * injection H as H1 H2. subst.
          auto.
        * tauto.
      + destruct (contains_id t2 i) eqn:I2.
        * right. left.
          assert (I': contains_id (Branch t1 t2) i = true) by
            (simpl; rewrite I2; apply Bool.orb_true_r).
          apply contains_valid_id in I2, I'.
          specialize (XOR t1 t2 i Hids I').
          exists t2.
          rewrite <- split_on_invalid_id with (t:=t1) in H.
          -- injection H as H1 H2. subst.
             auto.
          -- tauto.
        * left.
          exists t1.
          rewrite <- split_on_invalid_id with (t:=t1) in *.
          rewrite <- split_on_invalid_id with (t:=t2) in H.
          injection H as H1 H2. subst.
          auto.
          all: apply not_contains_valid_id in I1, I2; auto.     
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
    (*- destruct (contains_id t1 i); simpl; try congruence.*)
    - destruct (id0 =? i); simpl; try congruence.
  Qed.

  (*** Split: Validity of resulting state *)

  Lemma split_is_not_Stump : forall t i i',
      t <> Stump -> (split_in_tree i i' t) <> Stump.
  Proof.
    intros t i i' H.
    destruct t; simpl; try congruence.
    - destruct (id =? i); congruence.
  Qed.

  Lemma split_valid_structure : forall t i i',
      is_valid_tree_structure t ->
      is_valid_tree_structure (split_in_tree i i' t).
  Proof.
    intros t i i'; induction t; intros Hs; auto.
    - simpl split_in_tree.
      simpl in Hs.
      apply node_of_child_with_valid_structure.
      + apply split_is_not_Stump.
        destruct t0; try contradiction; congruence.
      + intros d' c'.
        destruct (split_in_tree i i' t0) eqn:S; try congruence.
        apply split_is_node in S. destruct S as [c'' [S1 S2]].
        subst.
        contradiction.
      + apply IHt.
        destruct t0; try contradiction; auto.
    - simpl split_in_tree.
      simpl in Hs.
      apply branch_of_children_with_valid_structure.
      + apply split_is_not_Stump.
        destruct t1; try contradiction; congruence.
      + apply split_is_not_Stump.
        destruct t1, t2; try contradiction; congruence.
      + apply IHt1.
        apply branch_children_valid_struct in Hs. tauto.
      + apply IHt2.
        apply branch_children_valid_struct in Hs. tauto.
    - simpl in *.
      destruct (id =? i); simpl; auto.
  Qed.

  Lemma split_ids : forall t i i',
      is_valid_tree_ids t ->
      ~ is_valid_id t i' ->
      is_valid_id t i ->
      Permutation (i' :: (get_all_ids t)) (get_all_ids (split_in_tree i i' t)).
  Proof.
    intros t; induction t; intros i i' Hids H' H; simpl in *.
    - contradiction.
    - auto.
    - pose proof valid_id_branch_xor as XOR.
      destruct (contains_id t1 i) eqn:I; simpl in *.
      + rewrite app_comm_cons.
        apply Permutation_app.
        * apply IHt1.
          -- apply valid_ids_branch in Hids. tauto.
          -- tauto.
          -- apply contains_valid_id.
             assumption.
        * specialize (XOR t1 t2 i Hids H).
          apply contains_valid_id in I.
          rewrite <- split_on_invalid_id; try tauto.
          apply Permutation_refl.
      + econstructor.
        * eapply Permutation_middle.
        * apply Permutation_app.
          -- specialize (XOR t1 t2 i Hids H).
             apply not_contains_valid_id in I.
             rewrite <- split_on_invalid_id; try tauto.
             apply Permutation_refl.
          -- apply IHt2.
             ++ apply valid_ids_branch in Hids. tauto.
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
    intros t; induction t; intros i i' Hin Hids; simpl in *.
    - assumption.
    - unfold is_valid_tree_ids in *; simpl in *.
      auto.
    - unfold is_valid_tree_ids in *; simpl in *.
      destruct (contains_id (Branch t1 t2) i) eqn:I; simpl in *.
      + apply Bool.orb_prop in I.
        repeat rewrite contains_valid_id in I.
        pose proof valid_id_branch_xor as XOR.
        specialize (XOR t1 t2 i Hids I).
        destruct I as [I | I].
        * eapply Permutation_NoDup.
          -- eapply Permutation_app_tail.
             eapply split_ids; try tauto.
             apply valid_ids_branch in Hids. tauto.
          -- rewrite <- app_comm_cons.
             rewrite <- split_on_invalid_id with (t:=t2) in *; try tauto.
             apply NoDup_cons; auto.
             rewrite in_app_iff.
             repeat rewrite <- valid_in_ids.
             tauto.
        * eapply Permutation_NoDup.
          -- eapply Permutation_app_head.
             eapply split_ids; try tauto.
             apply valid_ids_branch in Hids. tauto.
          -- rewrite <- split_on_invalid_id with (t:=t1) in *; try tauto.
             apply NoDupHelpers.no_dup_remove;
               try rewrite <- valid_in_ids;
               try tauto.
      + apply Bool.orb_false_iff in I.
        repeat rewrite not_contains_valid_id in I.
        repeat rewrite <- split_on_invalid_id; try tauto.
    - destruct (id =? i).
      unfold is_valid_tree_ids in *; simpl in *.
      + unfold not in Hin.
        destruct (i' =? id) eqn:I. 
        * apply Nat.eqb_eq in I. rewrite I in *.
          tauto.
        * apply Nat.eqb_neq in I.
          apply NoDupHelpers.no_dup_two.
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
    - rewrite IHt1 by assumption.
      rewrite IHt2 by assumption.
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

  (* i does not need to be valid, because the tree is unchanged if it is not *)
  Lemma split_get_new_leaf: forall t p i i' o,
      ~ is_valid_id t i' ->
      is_valid_tree_ids t ->
      is_valid_tree_structure t ->
      let t' := split_in_tree i i' t in
      get_compressed_data_in_tree' i' t' p o = get_compressed_data_in_tree' i t p o.
  Proof.
    intros t. induction t; intros param i i' o H Hids Hs; simpl in *.
    - reflexivity.
    - destruct o; simpl; apply IHt; auto;
        destruct t0; try contradiction; auto.
    - rewrite IHt1; try tauto.
      rewrite IHt2; try tauto.
      1, 3: apply valid_ids_branch in Hids; tauto.
      all: apply branch_children_valid_struct in Hs; tauto.
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

  (** Delete properties *)

  (* delete : preconds -> not is valid id on new tree, get on all other ids unchanged. *)

  Print delete_in_tree.

  Lemma is_branch_with_invalid_id : forall t id,
      ~ is_valid_id t id ->
      is_branch_with_id id t = false.
  Proof.
    intros t id H.
    induction t; simpl in *; auto.
    - apply Nat.eqb_neq in H. assumption.
  Qed.

  Lemma delete_on_invalid_id : forall t id p,
      is_valid_tree_structure t ->
      ~ is_valid_id t id ->
      delete_in_tree id t p = t.
  Proof.
    intros t id param; induction t; intros Hs H; simpl in *; auto.
    - rewrite IHt; auto;
        destruct t0; simpl in *; try contradiction; congruence.
    - repeat rewrite is_branch_with_invalid_id; auto.
      rewrite IHt1; try rewrite IHt2; try tauto.
      all: apply branch_children_valid_struct in Hs; tauto.
    - apply Nat.eqb_neq in H. rewrite H. reflexivity.
  Qed.

  Lemma delete_is_stump : forall t id p,
      is_valid_tree_structure t ->
      delete_in_tree id t p = Stump ->
      t = Stump \/ t = Leaf id \/ (exists d, t = Node d (Leaf id)).
  Proof.
    intros t i param; induction t; intros Hs H; simpl in *.
    - left. reflexivity.
    - right. right.
      exists data.
      destruct (delete_in_tree i t0 param) eqn:D; try congruence.
      destruct t0 eqn:T0; try contradiction; specialize (IHt Hs H);
        destruct IHt as [k | [k | [d k]]]; try congruence.
    - destruct (is_branch_with_id i t1) eqn:B1; simpl in *.
      + apply is_branch_with_id_struct in B1.
        * subst. destruct t1; try contradiction; congruence.
        * apply branch_children_valid_struct in Hs. tauto.
      + destruct (is_branch_with_id i t2) eqn:B2; simpl in *.
        * subst. contradiction.
        * congruence.
    - right. left.
      destruct (id =? i) eqn:I.
      + apply Nat.eqb_eq in I. congruence.
      + congruence.
  Qed.

  Lemma delete_is_branch : forall t p i l r,
      is_valid_tree_structure t ->
      is_valid_tree_ids t ->
      delete_in_tree i t p = Branch l r ->
      (* children are not branch with id *)
      (exists l', t = Branch l' r /\ l = delete_in_tree i l' p) \/
        (exists r', t = Branch l r' /\ r = delete_in_tree i r' p) \/
        (* children are branch with id *)
        (exists l', t = Branch l' (Branch l r) /\ is_branch_with_id i l' = true) \/
        (exists r', t = Branch (Branch l r) r' /\ is_branch_with_id i r' = true).
  Proof.
    intros t param i. induction t; intros l r Hs Hids H; simpl in *; try congruence.
    - destruct (delete_in_tree i t0 param); congruence.
    - pose proof valid_id_branch_xor as XOR.
      destruct (contains_id t1 i) eqn:I1.
      + destruct (is_branch_with_id i t1) eqn:B1.
        * right. right. left.
          exists t1.
          split; congruence.
        * destruct (is_branch_with_id i t2) eqn:B2.
          -- right. right. right.
             exists t2.
             split; congruence.
          -- left.
             assert (I: contains_id (Branch t1 t2) i = true) by
               (simpl; rewrite I1; apply Bool.orb_true_l).
             apply contains_valid_id in I1, I.
             specialize (XOR t1 t2 i Hids I).
             exists t1.
             rewrite delete_on_invalid_id with (t:=t2) in H.
             ** injection H as H1 H2. subst.
                split; auto.
             ** apply branch_children_valid_struct in Hs. tauto.
             ** tauto.
      + destruct (contains_id t2 i) eqn:I2.
        * apply not_contains_valid_id in I1.
          pose proof is_branch_with_invalid_id as B1. specialize (B1 _ _ I1). rewrite B1 in H.
          destruct (is_branch_with_id i t2) eqn:B2.
          -- right. right. right.
             exists t2.
             split; congruence.
          -- right. left.
             assert (I: contains_id (Branch t1 t2) i = true) by
               (simpl; rewrite I2; apply Bool.orb_true_r).
             apply contains_valid_id in I2, I.
             specialize (XOR t1 t2 i Hids I).
             exists t2.
             rewrite delete_on_invalid_id with (t:=t1) in H.
             ++ injection H as H1 H2. subst.
                auto.
             ++ apply branch_children_valid_struct in Hs. tauto.
             ++ tauto.
        * left.
          apply not_contains_valid_id in I1, I2.
          apply branch_children_valid_struct in Hs.
          exists t1.
          rewrite delete_on_invalid_id with (t:=t1) in *; try tauto.
          rewrite delete_on_invalid_id with (t:=t2) in H; try tauto.
          apply is_branch_with_invalid_id in I1, I2.
          rewrite I1, I2 in H.
          injection H as H1 H2.
          split; congruence.
    - destruct (id =? i); congruence.
  Qed.

  Lemma delete_is_branch' : forall t p i l r,
      is_valid_tree_structure t ->
      delete_in_tree i t p = Branch l r ->
      t = Branch l r \/
        (exists l' r', t = Branch l' r' /\
                         (is_branch_with_id i l' = true /\ r' = Branch l r \/
                            is_branch_with_id i r' = true /\ l' = Branch l r)).
  Proof.
    intros t param i. induction t; intros l r Hs H; simpl in *; try congruence.
    - destruct (delete_in_tree i t0 param); congruence.
    - destruct (contains_id (Branch t1 t2) i) eqn:I; simpl in I.
      + right.
        destruct (is_branch_with_id i t1) eqn:B1.
        * exists t1, t2.
          split; try reflexivity.
          left. split; auto.
        * destruct (is_branch_with_id i t2) eqn:B2.
          -- exists t1, t2.
             split; try reflexivity.
             right. split; auto.
          -- apply branch_children_valid_struct in Hs.
        admit.
      + left.
        apply Bool.orb_false_iff in I. destruct I as [I1 I2].
        rewrite not_contains_valid_id in I1, I2.
        rewrite delete_on_invalid_id in H; auto. rewrite delete_on_invalid_id in H; auto.
        apply is_branch_with_invalid_id in I1, I2.
        rewrite I1, I2 in H.
        assumption.
        all: apply branch_children_valid_struct in Hs; tauto.
    - destruct (id =? i); congruence.
  Admitted.

  Lemma delete_is_leaf : forall t p i j,
      is_valid_tree_structure t ->
      delete_in_tree i t p = Leaf j ->
      (t = Leaf j /\ i <> j) \/
        (exists l r, t = Branch l r /\
                       (is_branch_with_id i l = true /\ r = Leaf j \/
                          is_branch_with_id i r = true /\ l = Leaf j)).
  Proof.
    intros t param i j; induction t; intros Hs H; simpl in *; try congruence.
    - destruct (delete_in_tree i t0 param); congruence.
    - right.
      exists t1, t2.
      split; try reflexivity.
      destruct (is_branch_with_id i t1) eqn:B1.
      + left. split; congruence.
      + destruct (is_branch_with_id i t2) eqn:B2.
        * right. split; congruence.
        * congruence.          
    - left.
      destruct (id =? i) eqn:I.
      + apply Nat.eqb_eq in I. congruence.
      + apply Nat.eqb_neq in I.
        split; try assumption.
        injection H as H.
        lia.
  Qed.

  Definition is_branch_with_id_prop id t : Prop :=
    match is_branch_with_id id t with
    | true => True
    | _ => False
    end.

  Lemma delete_is_node : forall t id p d c,
      delete_in_tree id t p = Node d c ->
      (forall d' c', t <> Node d' c') -> 
        (exists l r, t = Branch l r /\
                       (is_branch_with_id_prop id l /\ r = Node d c \/
                          is_branch_with_id_prop id r /\ l = Node d c)).
  Proof.
    intros t; induction t; intros; simpl in *; try congruence.
    - exists t1, t2.
      split; auto.
      destruct (is_branch_with_id id t1) eqn:B1.
      + left. admit.
      + destruct (is_branch_with_id id t2) eqn:B2; try congruence.
        right. admit.
    - destruct (id =? id0); congruence.
  Admitted.

  Lemma delete_ids' : forall t p id,
      incl (get_all_ids (delete_in_tree id t p)) (get_all_ids t).
  Proof.
    intros t; induction t; intros param i; simpl in *.
    - apply incl_refl.
    - destruct (delete_in_tree i t0 param) eqn:D; auto.
      2, 3, 4: specialize (IHt param i); rewrite D in IHt; simpl in IHt; assumption.
      + apply incl_nil_l.
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
  Qed.

  Lemma Permutation_app_sym {A} : forall (l l' m : list A),
      Permutation (l ++ l') m ->
      Permutation (l' ++ l) m.
  Proof.
    intros.
    econstructor.
    - apply Permutation_app_comm.
    - assumption.
  Qed.

  Lemma get_all_ids_branch_with_id : forall t i,
      is_branch_with_id i t = true ->
      get_all_ids t = [i].
  Proof.
    intros t i.
    induction t; intros H; simpl in *; try congruence; auto.
    apply Nat.eqb_eq in H; subst; reflexivity.
  Qed.
  
  Lemma delete_ids : forall t p id,
      is_valid_tree_structure t ->
      is_valid_tree_ids t ->
      get_all_ids (delete_in_tree id t p) = get_all_ids t \/
        Permutation (get_all_ids t) (id :: get_all_ids (delete_in_tree id t p)).
  Proof.
    intros t; induction t; intros param i Hs H; simpl in *.
    - left. reflexivity.
    - destruct (contains_id t0 i) eqn:I.
      + destruct (delete_in_tree i t0 param) eqn:D; simpl in *.
        * right.
          apply delete_is_stump in D.
          destruct D as [D | [D | [d D]]]; subst; simpl; try contradiction.
          -- apply Permutation_refl.
          -- destruct t0; simpl in *; try contradiction; congruence.
        * apply delete_is_node in D. destruct D as [l [r [D D']]]. subst. simpl.
          admit. admit.
        * (* TODO delete is branch -> branch (2 poss) *)
          apply delete_is_branch in D.
          unfold is_valid_tree_ids in *. simpl in *.
          destruct D as [[l' [D D']] | [[r' [D D']] | [[l' [D D']] | [r' [D D']]]]];
            rewrite D; simpl.
          -- admit. (* use IH*)
          -- admit. (* use IH*)
          -- right.
             apply get_all_ids_branch_with_id in D'.
             rewrite D'. simpl.
             apply Permutation_refl.
          -- right.
             apply get_all_ids_branch_with_id in D'.
             rewrite D'. simpl.
             apply Permutation_app_sym.
             simpl.
             apply Permutation_refl.
          -- destruct t0; try contradiction; tauto.
          -- auto.
        * apply delete_is_leaf in D. destruct D as [[D D'] | [l [r [D D']]]].
          -- subst. simpl in *. apply Nat.eqb_eq in I. congruence.
          -- right.
             destruct D' as [[Db Dl] | [Db Dl]];
               apply get_all_ids_branch_with_id in Db; subst; simpl; rewrite Db; simpl.
             apply Permutation_refl.
             apply Permutation_rev.
          -- destruct t0; simpl in *; try contradiction; congruence.
      + left.
        apply not_contains_valid_id in I.
        rewrite delete_on_invalid_id; auto;
          destruct t0; simpl in *; try contradiction; auto.
    - destruct (is_branch_with_id i) eqn:B1.
      + right.
        apply is_branch_with_id_struct in B1.
        destruct B1 as [B1 | [d B1]]; subst; simpl in *; apply Permutation_refl.
        apply branch_children_valid_struct in Hs. tauto.
      + destruct (is_branch_with_id i t2) eqn:B2.
        * right.
          apply is_branch_with_id_struct in B2.
          destruct B2 as [B2 | [d B2]]; subst; simpl in *;
            apply Permutation_app_sym; simpl; apply Permutation_refl.
          apply branch_children_valid_struct in Hs. tauto.
        * unfold is_valid_tree_ids in *. simpl in H.
          specialize (IHt1 param i); specialize (IHt2 param i); simpl in *.
          destruct IHt1 as [IHt1 | IHt1]; destruct IHt2 as [IHt2 | IHt2]; simpl in *.
          1, 3, 4, 5, 9, 13: apply branch_children_valid_struct in Hs; tauto.
          1, 2, 5, 8: apply NoDup_app_remove_l with (l:=get_all_ids t1); auto.
          1, 2: apply NoDup_app_remove_r with (l':=get_all_ids t2); auto.
          -- left. congruence.
          -- right.
             rewrite IHt1.
             apply perm_trans with
               (l':= get_all_ids t1 ++ i :: get_all_ids (delete_in_tree i t2 param)).
             ++ apply Permutation_app_head. assumption.
             ++ apply Permutation_sym. apply Permutation_middle.
          -- right.
             rewrite IHt2.
             rewrite app_comm_cons.
             apply Permutation_app_tail.
             assumption.
          -- apply Permutation_sym in IHt1, IHt2.
             apply Permutation_in with (x:=i) in IHt1; try apply in_eq.
             apply Permutation_in with (x:=i) in IHt2; try apply in_eq.
             apply NoDupHelpers.no_dup_in_app with (a:=i) in H.
             ++ contradiction.
             ++ assumption.
    - destruct (id =? i) eqn:I; simpl.
      + right.
        apply Nat.eqb_eq in I. subst.
        repeat constructor.
      + left.
        reflexivity.
  Admitted.
        
  Lemma delete_valid_ids : forall t p id,
      is_valid_tree_structure t ->
      is_valid_tree_ids t ->
      is_valid_tree_ids (delete_in_tree id t p).
  Proof.
    intros t p i Hs H. unfold is_valid_tree_ids in *. simpl in *.
    pose proof delete_ids as D.
    specialize (D t p i Hs H).
    destruct D as [D | D].
    - congruence.
    - apply Permutation_NoDup in D; auto.
      apply NoDup_cons_iff in D.
      tauto.
  Qed.
        
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

  Lemma delete_get_on_deleted : forall t p i j,
      is_valid_state (t, p) ->
      is_valid_id t i ->
      let s' := delete i (t, p) in
      get_compressed_data j s' = None.
  Admitted.

  Lemma delete_unchanged : forall t p i j o,
      is_valid_state (t, p) ->
      is_valid_id t i ->
      i <> j ->
      get_compressed_data j (t, p) = o ->
      let s' := delete i (t, p) in
      get_compressed_data j s' = o.
  Admitted.

  (* TODO add to validity: define validity for CData and check for each node *)

End VT.
