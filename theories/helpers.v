From stdpp Require Import list.

Section slice.
  Context {A : Type}.
  Implicit Types l : list A.

  Definition slice l a b := take b (drop a l).
End slice.