
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

  Definition zipWith {A} {B} {C} (a : t A) (b: t B) (f : (A * B) -> C) : t C :=
    map f (combine a b).

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
  Definition merge_arrays (a1 a2 : Array.t val) : Array.t val :=
    Array.zipWith a1 a2 (fun x =>
                           match x with
                           | (x1, None) => x1
                           | (_, Some v) => Some v
                           end).

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

  (* t1 is old, t2 is recent *)
  Definition compress (p: p) (t1: t) (t2: t): t :=
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
        if Nat.leb (length l) p
        then
          let (a_cp, a_clk) := add_list_to_arrays l (Array.make p None) (Array.make p None) in
          Complete a_cp a_clk
        else Incomplete l
    end.

  Lemma merge_arrays_assoc : forall x y z,
      merge_arrays x (merge_arrays y z) = merge_arrays (merge_arrays x y) z.
  Proof.
    intros x y z.
    unfold merge_arrays.
  Admitted.

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

