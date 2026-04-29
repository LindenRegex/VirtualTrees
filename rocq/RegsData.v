
Require Import CData.

From Stdlib Require Import Arith Lia List.
Import ListNotations.

(* Arrays *)
Module Array.
  Definition t (A : Type) : Type := list A.

  (* Operations *)

  Definition length {A} (a: t A) : nat := length a.

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
  
  Definition merge_arrays (a1 a2 : Array.t val) : Array.t val :=
    Array.zipWith a1 a2 get_most_recent.

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

  Fixpoint add_list_to_array (l: list (nat * val))
    (a: Array.t val) : (Array.t val) :=
    match l with
    | [] => a
    | (i, e) :: l' =>
        let a' := add_list_to_array l' a in
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

  Fixpoint add_array_to_list (l: list (nat * val))
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
        add_array_to_list l' a'
    end.

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
        let a_cp := add_list_to_array (map all_to_cp l2) a_cp1 in
        let a_clk := add_list_to_array (map all_to_clk l2) a_clk1 in
        Complete a_cp a_clk
    | Incomplete l1, Complete a_cp2 a_clk2 =>
        let a_cp := add_array_to_list (map all_to_cp l1) a_cp2 in
        let a_clk := add_array_to_list (map all_to_clk l1) a_clk2 in
        Complete a_cp a_clk
    | Incomplete l1, Incomplete l2 =>
        let l := l2 ++ l1 in
        if Nat.leb p (length l)
        then
          let a_cp := add_list_to_array (map all_to_cp l) (Array.make p None) in
          let a_clk := add_list_to_array (map all_to_clk l) (Array.make p None) in
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

  Lemma add_list_to_array_length : forall l a,
      Array.length a = Array.length (add_list_to_array l a).
  Proof.
    intros l a.
    induction l as [ | [i e] l]; simpl.
    - reflexivity.
    - destruct e eqn:E.
      + rewrite Array.length_set.
        assumption.
      + assumption.
  Qed.

  Lemma add_array_to_list_length : forall l a,
      Array.length a = Array.length (add_array_to_list l a).
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
    - repeat rewrite <- add_list_to_array_length.
      assumption.
    - repeat rewrite <- add_array_to_list_length.
      assumption.
    - destruct (p <=? length (ly ++ lx)) eqn:L; simpl.
      + repeat rewrite <- add_list_to_array_length.
        split; apply Array.length_make.
      + split.
        * apply leb_complete_conv in L.
          assumption.
        * apply Forall_app.
          destruct Hx as [_ Hx]. destruct Hy as [_ Hy].
          split; assumption.
  Qed.
  
  Lemma merge_arrays_assoc : forall x y z,
      merge_arrays x (merge_arrays y z) = merge_arrays (merge_arrays x y) z.
  Proof.
    intros x y z.
    unfold merge_arrays.
    apply Array.zipWith_assoc.
    apply get_most_recent_assoc.
  Qed.

  Lemma compress_assoc : forall x y z p,
      compress p x (compress p y z) = compress p (compress p x y) z.
  Proof.
    intros x y z p.
    destruct x as [cpx clkx | lx], y as [cpy clky | ly], z as [cpz clkz | lz].
    - simpl.
      repeat rewrite merge_arrays_assoc.
      reflexivity.
    - (* might do a function for single array and separate *)
  Admitted.
  
End RegsData.

