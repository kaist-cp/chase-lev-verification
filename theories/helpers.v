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

  (* l[i..j-1] *)
  Definition slice l i j := take (j-i) (drop i l).

  Lemma slice_to_nil xl i j : (i >= j) → slice xl i j = [].
  Proof.
    unfold slice. intros H.
    replace (j-i) with 0 by lia. auto.
  Qed.

  Lemma slice_insert_right l i j k v :
    j ≤ k →
    slice (<[k:=v]> l) i j = slice l i j.
  Proof.
    unfold slice. intros H.
    destruct (decide (i ≤ j)).
    - rewrite drop_insert_le; [|lia].
      rewrite take_insert; auto. lia.
    - replace (j-i) with 0 by lia. auto.
  Qed.

  Lemma slice_extend_right l i j v :
    i <= j → l !! j = Some v →
    slice l i (S j) = slice l i j ++ [v].
  Proof.
    unfold slice. intros Hij Hj.
    replace (S j - i) with (S (j - i)) by lia.
    rewrite (take_S_r _ _ v); auto. rewrite lookup_drop.
    replace (i + (j - i)) with j by lia. auto.
  Qed.
End slice.
