
Require Import CData.

From Stdlib Require Import Arith Lia List.
Import ListNotations.

(* Arrays *)
Module Array.
  Definition t (A : Type) := list A.

  (* Operations *)

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
  Definition t : Set := nat.

  Definition p : Set := nat.

  Definition compress (p: p) (t1: t) (t2: t): t := t1 + t2.

  Definition is_valid (t: t) := True.

  Lemma compress_assoc : forall x y z p,
      compress p x (compress p y z) = compress p (compress p x y) z.
  Proof. 
    intros. simpl.
    unfold compress. lia.
  Qed.
  
End RegsData.

