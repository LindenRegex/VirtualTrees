
Require Import CData.

From Stdlib Require Import Arith Lia List.
Import ListNotations.

(* Arrays *)
Module Array.
  Definition t (A : Type) : Type := list A.

  (* Operations *)

  Definition length {A} (a: t A) : nat := length a.
  Definition In {A} (x: A) (a: t A) : Prop := In x a.

  Fixpoint make {A} (n : nat) (init : A) : t A :=
    match n with
    | 0 => []
    | S n' => init :: make n' init
    end.
  
  Definition get {A} (a : t A) (i : nat) : option A :=
    nth_error a i.

  Fixpoint set {A} (a : t A) (i : nat) (x : A) : t A :=
    match a, i with
    | [], _ => []
    | _ :: xs, 0 => x :: xs
    | y :: xs, S i' => y :: set xs i' x
    end.

  Fixpoint zipWith {A} {B} {C} (a: t A) (b: t B) (f : A -> B -> C) : t C :=
    match a, b with
    | [], _ => []
    | _, [] => []
    | a0 :: a', b0 :: b' => (f a0 b0) :: (zipWith a' b' f)
    end.

  (* Properties *)

  Lemma length_make {A} : forall (n : nat) (x : A),
      length (make n x) = n.
  Proof.
    induction n; intros; simpl; auto.
  Qed.

  Lemma length_set {A} : forall (a : t A) (i : nat) (x : A),
      length (set a i x) = length a.
  Proof.
    induction a; intros; simpl.
    - reflexivity.
    - destruct i; simpl; auto.
  Qed.

  Lemma get_make {A} : forall (n : nat) (x : A) (i : nat),
      i < n ->
      get (make n x) i = Some x.
  Proof.
    induction n; intros; simpl in *.
    - lia.
    - destruct i; simpl.
      + reflexivity.
      + apply IHn.
        lia.
  Qed.

  Lemma get_make_invalid {A} : forall (n : nat) (x : A) i,
      i >= n ->
      get (make n x) i = None.
  Proof.
    induction n; intros; simpl in *.
    - destruct i; simpl; reflexivity.
    - destruct i; simpl.
      + lia.
      + apply IHn.
        lia.
  Qed.

  Lemma get_invalid {A} : forall n (a: t A),
      get a n = None <-> n >= length a.
  Proof.
    split; intros; apply nth_error_None; assumption.
  Qed.

  Lemma in_make {A} : forall (x: A) (a: A) (size: nat),
      In x (make size a) -> x = a.
  Proof.
    induction size; intros Hin; simpl in *.
    - contradiction.
    - destruct Hin as [Hin | Hin]; auto.
  Qed.

  Lemma get_valid {A} : forall (a: t A) i,
      0 <= i /\ i < length a <->
      (exists x, get a i = Some x).
  Proof.
    split; intros.
    - destruct (nth_error a i) eqn:Hnth.
      + exists a0.
        exact Hnth.
      + apply nth_error_None in Hnth.
        unfold length in *.
        lia.
    - destruct H as [x H].
      destruct (Nat.leb (length a) i) eqn:I.
      + apply Nat.leb_le in I.
        apply nth_error_None in I.
        unfold get in H.
        congruence.
      + apply Nat.leb_gt in I.
        lia.
  Qed.

  Lemma set_invalid {A} : forall (a: t A) i x,
      i >= length a ->
      set a i x = a.
  Proof.
    induction a; intros; simpl in *.
    - reflexivity.
    - destruct i; simpl in *.
      + lia.
      + rewrite IHa.
        * reflexivity.
        * lia.
  Qed.

  Lemma set_comm {A} : forall (a: t A) i j x y,
      i <> j ->
      set (set a i x) j y = set (set a j y) i x.
  Proof.
    induction a; intros; simpl in *; auto.
    destruct i; destruct j; auto.
    - congruence.
    - simpl.
      rewrite IHa; auto.
  Qed.

  Lemma get_set_eq {A} : forall (a : t A) i x,
      i < length a ->
      get (set a i x) i = Some x.
  Proof.
    induction a; intros; simpl in *.
    - lia.
    - destruct i; simpl.
      + reflexivity.
      + apply IHa.
        lia.
  Qed.

  Lemma get_set_neq {A} : forall (a : t A) i j x,
      i <> j ->
      get (set a i x) j = get a j.
  Proof.
    induction a; intros; simpl in *.
    - destruct j; simpl; reflexivity.
    - destruct i; destruct j; simpl.
      + lia.
      + reflexivity.
      + reflexivity.
      + apply IHa.
        lia.
  Qed.

  Lemma set_get {A} : forall a i (x: A),
      get a i = Some x -> set a i x = a.
  Proof.
    induction a; intros i x H; simpl in *; auto.
    destruct i; simpl in *.
    - injection H as H. congruence.
    - rewrite IHa; auto.
  Qed.

  Lemma get_neq_set {A} : forall a i j (x y: A),
      get (set a i x) j = Some y ->
      x <> y ->
      get a j = Some y.
  Proof.
    intros a i j x y H Hxy; simpl in *.
    destruct (Nat.leb (length a) j) eqn:J.
    - apply Nat.leb_le in J.
      erewrite <- length_set with (i:=i) (x:= x) in J.
      apply nth_error_None in J.
      unfold get in *.
      congruence.
    - apply Nat.leb_gt in J.
      destruct (i =? j) eqn:Hij.
      + apply Nat.eqb_eq in Hij. subst.
        rewrite get_set_eq in H; auto.
        injection H as H. congruence.
      + apply Nat.eqb_neq in Hij.
        rewrite get_set_neq in H; auto.
  Qed.

  Lemma zipWith_length {A} {B} {C} : forall (a : t A) (b : t B) (f : A -> B -> C),
      length (zipWith a b f) = min (length a) (length b).
  Proof.
    induction a; intros b f; simpl.
    - reflexivity.
    - destruct b eqn:Bl; simpl.
      + reflexivity.
      + rewrite IHa.
        reflexivity.
  Qed.

  Lemma zipWith_assoc {A} : forall (a b c: t A) (f : A -> A -> A),
      (forall x y z, f x (f y z) = f (f x y) z) ->
      zipWith a (zipWith b c f) f = zipWith (zipWith a b f) c f.
  Proof.
    induction a; intros b c f Hf; simpl.
    - reflexivity.
    - destruct b eqn:B; simpl.
      + reflexivity.
      + destruct c eqn:C.
        * reflexivity.
        * rewrite Hf.
          rewrite IHa; auto.
  Qed.

  Lemma zipWith_neutral_r {A} {B} : forall (a: t A) (b: t B) (f: A -> B -> A),
      (forall x y, In y b -> f x y = x) ->
      length a <= length b ->
      zipWith a b f = a.
  Proof.
    induction a; intros b f Hf Hl; simpl.
    - reflexivity.
    - destruct b eqn:V; simpl in *.
      + lia.
      + rewrite IHa.
        * rewrite Hf.
          -- reflexivity.
          -- left. reflexivity.
        * intros x y.
          specialize (Hf x y).
          tauto.
        * lia.
  Qed.

  Lemma zipWith_neutral_l {A} {B} : forall (a: t A) (b: t B) (f: A -> B -> B),
      (forall x y, In x a -> f x y = y) ->
      length a >= length b ->
      zipWith a b f = b.
  Proof.
    induction a; intros b f Hf Hl; simpl in *.
    - destruct b; simpl in *.
      + reflexivity.
      + lia.
    - destruct b eqn:V; simpl in *.
      + reflexivity.
      + rewrite IHa.
        * rewrite Hf.
          -- reflexivity.
          -- left. reflexivity.
        * intros x y.
          specialize (Hf x y).
          tauto.
        * lia.
  Qed.

  Lemma different_at_head_same_tails {A} : forall (a0 b0 : A) a b,
      (forall j : nat, j <> 0 -> get (a0 :: a) j = get (b0 :: b) j) ->
      a = b.
  Proof.
    intros a0 b0 a b H.
    apply nth_error_ext.
    intros n.
    specialize (H (S n)).
    simpl in *.
    auto.
  Qed.

  Lemma different_at_some_cons {A} : forall n (a0 b0 : A) a b,
      (forall j : nat, j <> S n -> get (a0 :: a) j = get (b0 :: b) j) ->
      (forall j : nat, j <> n -> get a j = get b j).
  Proof.
    intros n a0 b0 a b H j Hj.
    specialize (H (S j)).
    simpl in *.
    auto.
  Qed.

  Lemma different_at_succ_same_head {A} : forall n (a0 b0 : A) a b,
      (forall j : nat, j <> S n -> get (a0 :: a) j = get (b0 :: b) j) ->
      a0 = b0.
  Proof.
    intros n a0 b0 a b H.
    specialize (O_S n) as Hn.
    specialize (H 0 Hn).
    simpl in *.
    injection H as H.
    assumption.
  Qed.      
  
  Lemma zipWith_in {A} {B} {C} : forall (a: t A) (b b': t B) (f: A -> B -> C) i x y,
      get b i = Some x ->
      get a i = Some y ->
      length b = length b' ->
      (forall j, j <> i -> get b j = get b' j) ->
      zipWith a b f = set (zipWith a b' f) i (f y x).
  Proof.
    induction a; intros b b' f i x y Hb Ha Hl H; simpl in *; auto.
    destruct b eqn:LB; simpl in *.
    - destruct i; simpl in Hb; congruence.
    - destruct b' eqn:LB'; simpl in *.
      + congruence.
      + destruct i eqn:I; simpl in *.
        * injection Hb as Hb. injection Ha as Ha. subst.
          apply different_at_head_same_tails in H.
          congruence.
        * erewrite <- IHa; eauto.
          -- apply different_at_succ_same_head in H.
             congruence.
          -- eapply different_at_some_cons. eauto.
  Qed.

  Lemma zipWith_set_overwrite_r {A} {B} : forall a b xa xb (f: A -> B -> B) i,
      get b i = Some xb ->
      (forall x, f x xb = xb) ->
      zipWith (set a i xa) b f = zipWith a b f.
  Proof.
    induction a; intros b xa xb f i Hb Hf; simpl in *; auto.
    - destruct b eqn:LB.
      + destruct i; simpl in *; congruence.
      + destruct i eqn:I; simpl in *.
        * injection Hb as Hb. subst.
          congruence.
        * erewrite IHa; eauto.
  Qed.

  Lemma zipWith_set_overwrite_l {A} {B} : forall a b xa xb (f: A -> B -> A) i,
      get b i = Some xb ->
      (forall x, f x xb = x) ->
      zipWith (set a i xa) b f = set (zipWith a b f) i xa.
  Proof.
    induction a; intros b xa xb f i Hb Hf; simpl in *; auto.
    destruct b eqn:LB.
    - destruct i; simpl in *; congruence.
    - destruct i eqn:I; simpl in *.
      * injection Hb as Hb. subst.
        congruence.
      * erewrite IHa; eauto.
  Qed.
  
End Array.


(* Regsdata *)
Module RegsData : CDATA.
  Definition val : Type := option nat.
  
  Inductive t' : Type :=
  | Complete (a_cp: Array.t val) (a_clk: Array.t val)
  | Incomplete (l: list (nat * val * val)).

  Definition t := t'.
  Definition p : Set := nat.

  Definition is_valid_index (p: p) (i: nat) : Prop :=
    0 <= i /\ i < p.

  Definition get_index (e: nat * val * val) : nat :=
    match e with
    | (i, _, _ ) => i
    end.

  Definition is_valid (p: p) (t: t) : Prop :=
    match t with
    | Complete a_cp a_clk =>
        Array.length a_cp = p /\ Array.length a_clk = p
    | Incomplete l =>
        length l < p /\ Forall (fun x => is_valid_index p (get_index x)) l
    end.

  (* a1 is older than a2 -> overwrite a1 with a2 
   don't overwrite if a2 element is None *)
  Definition get_most_recent (old new : val) : val :=
    match new with
    | None => old
    | Some _ => new
    end.

  Lemma get_most_recent_assoc : forall x y z,
      get_most_recent x (get_most_recent y z) = get_most_recent (get_most_recent x y) z.
  Proof.
    intros x y z.
    destruct z; destruct y; simpl; reflexivity.
  Qed.
  
  Definition merge_arrays (a_old a_new : Array.t val) : Array.t val :=
    Array.zipWith a_old a_new get_most_recent.

  (* list is more recent than arrays
     closer to start of list => more recent 
     -> should add elements at the end of the list first, so that they can be overwritten later 
     don't overwrite if list element is None
   *)
  Fixpoint add_list_to_arrays (l: list (nat * val * val))
    (a_cp: Array.t val) (a_clk: Array.t val) : (Array.t val) * (Array.t val) :=
    match l with
    | [] => (a_cp, a_clk)
    | (i, cp, clk) :: l' =>
        let (a_cp', a_clk') := add_list_to_arrays l' a_cp a_clk in
        match cp, clk with
        | None, None => (a_cp', a_clk')
        | Some v_cp, None => (Array.set a_cp' i cp, a_clk')
        | None, Some v_clk => (a_cp', Array.set a_clk' i clk)
        | Some v_cp, Some v_clk => (Array.set a_cp i cp, Array.set a_clk i clk)
        end
    end.

  Fixpoint merge_new_list_old_array (a: Array.t val) (l: list (nat * val)) : (Array.t val) :=
    match l with
    | [] => a
    | (i, e) :: l' =>
        let a' := merge_new_list_old_array a l' in
        match e with
        | None => a'
        | Some v => Array.set a' i e
        end
    end.

  (* array is more recent than list
   only add list elem if what what there before is None *)
  Fixpoint add_arrays_to_list (l: list (nat * val * val))
    (a_cp: Array.t val) (a_clk: Array.t val) : (Array.t val) * (Array.t val) :=
    match l with
    | [] => (a_cp, a_clk)
    | (i, cp, clk) :: l' =>
        (* add cp clk to arrays if what is already there is None *)
        let (a_cp', a_clk') :=
          match Array.get a_cp i, Array.get a_clk i with
          | Some None, Some None => (Array.set a_cp i cp, Array.set a_clk i clk)
          | Some None, _ => (Array.set a_cp i cp, a_clk)
          | _, Some None => (a_cp, Array.set a_clk i clk)
          | _, _ => (a_cp, a_clk)
          end in
        (* then recursively call *)
        add_arrays_to_list l' a_cp' a_clk'
    end.

  Fixpoint merge_new_array_old_list (l: list (nat * val))
    (a: Array.t val) : (Array.t val) :=
    match l with
    | [] => a
    | (i, e) :: l' =>
        (* add e to arrays if what is already there is None *)
        let a' :=
          match Array.get a i with
          | Some None => Array.set a i e
          | _ => a
          end in
        merge_new_array_old_list l' a'
    end.

  Definition list_to_array (size: nat) (l: list (nat * val)) : (Array.t val) :=
    merge_new_list_old_array (Array.make size None) l.

  (* t1 is old, t2 is recent *)
  Definition compress' (p: p) (t1: t) (t2: t): t :=
    match t1, t2 with
    | Complete a_cp1 a_clk1, Complete a_cp2 a_clk2 =>
        Complete (merge_arrays a_cp1 a_cp2) (merge_arrays a_clk1 a_clk2)
    | Complete a_cp1 a_clk1, Incomplete l2 =>
        let (a_cp, a_clk) := add_list_to_arrays l2 a_cp1 a_clk1 in
        Complete a_cp a_clk
    | Incomplete l1, Complete a_cp2 a_clk2 =>
        let (a_cp, a_clk) := add_arrays_to_list l1 a_cp2 a_clk2 in
        Complete a_cp a_clk
    | Incomplete l1, Incomplete l2 =>
        let l := l2 ++ l1 in
        if Nat.leb p (length l)
        then
          let (a_cp, a_clk) := add_list_to_arrays l (Array.make p None) (Array.make p None) in
          Complete a_cp a_clk
        else Incomplete l
    end.

  Definition all_to_cp (x : nat * val * val) : (nat * val) :=
    match x with
    | (i, cp, _) => (i, cp)
    end.

  Definition all_to_clk (x : nat * val * val) : (nat * val) :=
    match x with
    | (i, _, clk) => (i, clk)
    end.

  Definition compress (p: p) (t1: t) (t2: t): t :=
    match t1, t2 with
    | Complete a_cp1 a_clk1, Complete a_cp2 a_clk2 =>
        Complete (merge_arrays a_cp1 a_cp2) (merge_arrays a_clk1 a_clk2)
    | Complete a_cp1 a_clk1, Incomplete l2 =>
        let a_cp := merge_new_list_old_array a_cp1 (map all_to_cp l2) in
        let a_clk := merge_new_list_old_array a_clk1 (map all_to_clk l2) in
        Complete a_cp a_clk
    | Incomplete l1, Complete a_cp2 a_clk2 =>
        let a_cp := merge_new_array_old_list (map all_to_cp l1) a_cp2 in
        let a_clk := merge_new_array_old_list (map all_to_clk l1) a_clk2 in
        Complete a_cp a_clk
    | Incomplete l1, Incomplete l2 =>
        let l := l2 ++ l1 in
        if Nat.leb p (length l)
        then
          let a_cp := merge_new_list_old_array (Array.make p None) (map all_to_cp l) in
          let a_clk := merge_new_list_old_array (Array.make p None) (map all_to_clk l) in
          Complete a_cp a_clk
        else Incomplete l
    end.
  
  Lemma merge_arrays_length : forall a b,
      Array.length (merge_arrays a b) = min (Array.length a) (Array.length b).
  Proof.
    intros a b.
    unfold merge_arrays.
    apply Array.zipWith_length.
  Qed.

  Lemma merge_new_list_old_array_length : forall l a,
      Array.length a = Array.length (merge_new_list_old_array a l).
  Proof.
    intros l a.
    induction l as [ | [i e] l]; simpl.
    - reflexivity.
    - destruct e eqn:E.
      + rewrite Array.length_set.
        assumption.
      + assumption.
  Qed.

  Lemma merge_new_array_old_list_length : forall l a,
      Array.length a = Array.length (merge_new_array_old_list l a).
  Proof.
    intros l.
    induction l as [ | [i e] l]; intros a; simpl.
    - reflexivity.
    - destruct (Array.get a i) eqn:V.
      + destruct v eqn:V'.
        * apply IHl.
        * rewrite <- IHl.
          symmetry.
          apply Array.length_set.
      + apply IHl.
  Qed.

  Lemma compress_valid : forall x y p,
      is_valid p x ->
      is_valid p y ->
      is_valid p (compress p x y).
  Proof.
    intros x y p Hx Hy.
    destruct x as [cpx clkx | lx]; destruct y as [cpy clky | ly]; simpl in *.
    - destruct Hx as [Hcpx Hclkx]. destruct Hy as [Hcpy Hclky].
      split;
        rewrite merge_arrays_length;
        [rewrite Hcpx, Hcpy | rewrite Hclkx, Hclky];
        lia.
    - repeat rewrite <- merge_new_list_old_array_length.
      assumption.
    - repeat rewrite <- merge_new_array_old_list_length.
      assumption.
    - destruct (p <=? length (ly ++ lx)) eqn:L; simpl.
      + repeat rewrite <- merge_new_list_old_array_length.
        split; apply Array.length_make.
      + split.
        * apply leb_complete_conv in L.
          assumption.
        * apply Forall_app.
          destruct Hx as [_ Hx]. destruct Hy as [_ Hy].
          split; assumption.
  Qed.

  Lemma merge_arrays_new_is_None : forall a,
      merge_arrays a (Array.make (Array.length a) None) = a.
  Proof.
    intros a.
    unfold merge_arrays.
    apply Array.zipWith_neutral_r.
    - intros x y Hin.
      unfold get_most_recent.
      apply Array.in_make in Hin.
      rewrite Hin.
      reflexivity.
    - rewrite Array.length_make.
      lia.
  Qed.

  Lemma list_to_array_get_some : forall l size i n,
      0 <= i /\ i < size ->
      Array.get (list_to_array size ((i, Some n) :: l)) i = Some (Some n).
  Proof.
    intros; simpl.
    unfold list_to_array. simpl.
    apply Array.get_set_eq.
    rewrite <- merge_new_list_old_array_length.
    rewrite Array.length_make.
    lia.
  Qed.

  Lemma list_to_array_get_none1 : forall l size i o,
      i >= size ->
      Array.get (list_to_array size ((i, o) :: l)) i = Array.get (list_to_array size l) i.
  Proof.
    intros; simpl.
    unfold list_to_array. simpl.
    rewrite Array.set_invalid.
    + destruct o; reflexivity.
    + rewrite <- merge_new_list_old_array_length.
      rewrite Array.length_make.
      assumption.
  Qed.

  Lemma list_to_array_get_none2 : forall l size i,
      0 <= i /\ i < size ->
      Array.get (list_to_array size ((i, None) :: l)) i = Array.get (list_to_array size l) i.
  Proof.
    intros; simpl.
    unfold list_to_array. simpl.
    reflexivity.
  Qed.

  Lemma nat_pos_bounded : forall x y, x < y -> 0 <= x < y.
  Proof. lia. Qed.

  Lemma merge_arrays_from_list_some : forall a l i n,
      merge_arrays a (list_to_array (Array.length a) ((i, Some n) :: l)) =
        Array.set (merge_arrays a (list_to_array (Array.length a) l)) i (Some n).
  Proof.
    intros a l i n; simpl.
    unfold merge_arrays.
    (* destruct i valid*)
    destruct (Nat.leb (Array.length a) i) eqn:A.
    - apply Nat.leb_le in A.
      unfold list_to_array.
      simpl.
      repeat rewrite Array.set_invalid.
      + reflexivity.
      + rewrite Array.zipWith_length.
        rewrite <- merge_new_list_old_array_length.
        rewrite Array.length_make.
        lia.
      + rewrite <- merge_new_list_old_array_length.
        rewrite Array.length_make.
        lia.
    - apply Nat.leb_gt in A.
      pose proof nat_pos_bounded as B. specialize (B i (Array.length a) A).
      apply Array.get_valid in B.
      destruct B as [x B].
      erewrite Array.zipWith_in with (b':= list_to_array (Array.length a) l) (x:= Some n) (i:= i);
        eauto.
      + apply list_to_array_get_some.
        lia.
      + unfold list_to_array. simpl.
        rewrite Array.length_set.
        reflexivity.
      + intros j Hij.
        unfold list_to_array. simpl.
        apply Array.get_set_neq.
        auto.
  Qed.

  Lemma merge_arrays_from_list_none : forall a l i,
      merge_arrays a (list_to_array (Array.length a) ((i, None) :: l)) =
        merge_arrays a (list_to_array (Array.length a) l).
  Proof.
    intros a l i; simpl.
    unfold merge_arrays.
    unfold list_to_array.
    simpl.
    reflexivity.
  Qed.

  Lemma merge_new_list_old_array_equiv : forall l a,
      merge_new_list_old_array a l =
        merge_arrays a (list_to_array (Array.length a) l).
  Proof.
    induction l; intros arr; simpl in *.
    - unfold list_to_array. simpl.
      symmetry.
      apply merge_arrays_new_is_None.
    - destruct a as [i e].
      destruct e.
      + rewrite IHl.
        rewrite merge_arrays_from_list_some.
        reflexivity.
      + rewrite IHl.
        rewrite merge_arrays_from_list_none.
        reflexivity.
  Qed.

  Lemma merge_arrays_old_is_None : forall a,
      merge_arrays (Array.make (Array.length a) None) a = a.
  Proof.
    intros a.
    unfold merge_arrays.
    apply Array.zipWith_neutral_l.
    - intros x y Hin.
      unfold get_most_recent.
      apply Array.in_make in Hin.
      rewrite Hin.
      destruct y; reflexivity.
    - rewrite Array.length_make.
      lia.
  Qed.

  Lemma merge_new_array_old_list_set_array : forall l a x i,
      merge_new_array_old_list l (Array.set a i (Some x)) =
        Array.set (merge_new_array_old_list l a) i (Some x).
  Proof.
    induction l; intros arr x i; simpl in *; auto.
    destruct a as [j e].
    destruct (@Array.get val (@Array.set (option nat) arr i (@Some nat x)) j) eqn:A.
    - destruct v eqn:V; simpl in *.
      + destruct (i =? j) eqn:Hij.
        * apply Nat.eqb_eq in Hij. subst.
          (* j is valid *)
          (* destruct get arr j -> set later in j anyways *) 
          rewrite Array.get_set_eq in A.
          injection A as A. subst.
          admit. admit.
        * apply Nat.eqb_neq in Hij.
          rewrite Array.get_set_neq in A; auto.
          rewrite A.
          auto.
      + destruct (i =? j) eqn:Hij.
        * apply Nat.eqb_eq in Hij. subst.
          rewrite Array.get_set_eq in A; try congruence.
          erewrite <- Array.length_set.
          apply Array.get_valid.
          eauto.
        * apply Nat.eqb_neq in Hij.
          rewrite Array.get_set_neq in A; auto.
          rewrite A.
          rewrite Array.set_comm; auto.
    - apply Array.get_invalid in A.
      rewrite Array.length_set in A.
      apply Array.get_invalid in A.
      rewrite A.
      auto.      
  Admitted.

  Lemma merge_new_array_old_list_equiv : forall l a,
      merge_new_array_old_list l a =
        merge_arrays (list_to_array (Array.length a) l) a.
  Proof.
    induction l; intros arr; simpl in *.
    - unfold list_to_array. simpl.
      symmetry.
      apply merge_arrays_old_is_None.
    - destruct a as [i e].
      destruct (Array.get arr i) eqn:G.
      + destruct v eqn:V.
        * (* array overwrites list *)
          unfold list_to_array. simpl.
          destruct e eqn:E; simpl in *.
          -- unfold merge_arrays.
             rewrite Array.zipWith_set_overwrite_r with (xb:= Some n); auto.
          -- auto.
        * (* array has none, so list writes *)
          unfold list_to_array in *.
          unfold merge_arrays in *. simpl.
          destruct e eqn:E; simpl in *.
          -- rewrite Array.zipWith_set_overwrite_l with (xb:=None) (b:= arr); auto.
             rewrite <- IHl.
             apply merge_new_array_old_list_set_array.
          -- rewrite <- IHl.
             rewrite Array.set_get; auto.
      + (* i is out of bounds *)
        unfold list_to_array. simpl.
        destruct e eqn:E; simpl in *.
        * apply Array.get_invalid in G.
          rewrite Array.set_invalid; auto.
          rewrite <- merge_new_list_old_array_length.
          rewrite Array.length_make.
          assumption.
        * auto.
  Admitted.
  
  Lemma merge_arrays_assoc : forall x y z,
      merge_arrays x (merge_arrays y z) = merge_arrays (merge_arrays x y) z.
  Proof.
    intros x y z.
    unfold merge_arrays.
    apply Array.zipWith_assoc.
    apply get_most_recent_assoc.
  Qed.

  Lemma compress_assoc : forall x y z p,
      is_valid p x ->
      is_valid p y ->
      is_valid p z ->
      compress p x (compress p y z) = compress p (compress p x y) z.
  Proof.
    intros x y z p Hx Hy Hz.
    destruct x as [cpx clkx | lx], y as [cpy clky | ly], z as [cpz clkz | lz].
    - simpl.
      repeat rewrite merge_arrays_assoc.
      reflexivity.
    - simpl in *.
      destruct Hx as [Hx Hx'].
      destruct Hy as [Hy Hy'].
      rewrite merge_new_list_old_array_equiv.
      rewrite merge_new_list_old_array_equiv with (a:=clky).
      rewrite merge_new_list_old_array_equiv with (a:=(merge_arrays cpx cpy)).
      rewrite merge_new_list_old_array_equiv with (a:=(merge_arrays clkx clky)).
      repeat rewrite merge_arrays_assoc.
      repeat rewrite merge_arrays_length.
      rewrite Hx, Hx', Hy, Hy'.
      rewrite Nat.min_id.
      reflexivity.
      (* might do a function for single array and separate *)
  Admitted.
  
End RegsData.

