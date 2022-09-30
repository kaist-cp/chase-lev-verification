From stdpp Require Import list.

Section slice.
  Context {A : Type}.
  Implicit Types l : list A.

  (* k elements starting from i-th *)
  Definition slice l i k := take k (drop i l).

  Lemma slice_0 l i : slice l i 0 = [].
  Proof. auto. Qed.
End slice.
