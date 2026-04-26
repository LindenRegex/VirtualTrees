
Module Type CDATA.

  Parameter t : Type.

  Parameter p : Set.

  Parameter compress : p -> t -> t -> t.

  Parameter is_valid: p -> t -> Prop.

  (* TODO: add some axioms *)
  
  (* associativity *)
  Axiom compress_assoc : forall (x y z : t) (param: p),
      compress param x (compress param y z) = compress param (compress param x y) z.

End CDATA.
