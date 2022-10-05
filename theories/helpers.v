From stdpp Require Import list.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import proofmode notation.

Section heap.
  Context `{!heapGS Σ} (N : namespace).

  Lemma array_agree x l1 l2 dq1 dq2 :
    length l1 = length l2 →
    x ↦∗{dq1} l1 -∗ x ↦∗{dq2} l2 -∗ ⌜l1 = l2⌝.
  Proof.
    revert l2.
    iInduction l1 as [|v l1] "HInd" using rev_ind;
      iIntros (l2 HL) "x1 x2".
      { destruct l2; auto. }
    destruct l2 using rev_ind.
      { rewrite app_length in HL. simpl in HL. lia. }
    clear IHl2.

    do 2 rewrite array_app.
    assert (length l1 = length l2).
      { do 2 rewrite app_length in HL. simpl in HL. lia. }
    iDestruct "x1" as "[x1 xl1]". iDestruct "x2" as "[x2 xl2]".
    do 2 rewrite array_singleton. rewrite H.
    iDestruct (mapsto_agree with "xl1 xl2") as "<-".
    iDestruct ("HInd" $! l2 with "[] [x1] [x2]") as "<-"; auto.
  Qed.
End heap.

Section slice.
  Context {A : Type}.
  Implicit Types l : list A.

  (* k elements starting from i-th *)
  Definition slice l i k := take k (drop i l).

  Lemma slice_0 l i : slice l i 0 = [].
  Proof. auto. Qed.

  Lemma slice_insert_right l i k j v :
    j >= i + k →
    slice (<[j:=v]> l) i k = slice l i k.
  Proof.
    unfold slice. intros H.
    rewrite drop_insert_le; [|lia].
    rewrite take_insert; auto. lia.
  Qed.

  Lemma slice_extend_right l i k v :
    l !! (i+k) = Some v →
    slice l i (S k) = slice l i k ++ [v].
  Proof.
    unfold slice. intros H.
    rewrite (take_S_r _ _ v); auto.
    by rewrite lookup_drop.
  Qed.
End slice.
