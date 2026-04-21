
Require Import CData.

From Stdlib Require Import List.

Module VT (Data : CDATA).
  Import Data.

  Inductive VirtalTree := Admitted. (* the actal tree with root, branch, node and leaf *)

  (* Type state: counter + tree *)

  Definition empty := Admitted.

  Definition insert := Admitted.

  Definition split := Admitted.

  Definition delete := Admitted.

  Definition get_compressed_data := Admitted.

  Definition is_empty := Admitted.

End VT.
