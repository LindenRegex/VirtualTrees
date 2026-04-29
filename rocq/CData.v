
Module Type CDATA.

  Parameter t : Type.

  Parameter p : Set.

  Parameter compress : p -> t -> t -> t.

  Parameter is_valid: p -> t -> Prop.

  (* TODO: add some axioms *)

  (* validity after compression *)
  Axiom compress_valid : forall x y (p: p),
      is_valid p x ->
      is_valid p y ->
      is_valid p (compress p x y).
  
  (* associativity *)
  Axiom compress_assoc : forall (x y z : t) (param: p),
      compress param x (compress param y z) = compress param (compress param x y) z.

End CDATA.
