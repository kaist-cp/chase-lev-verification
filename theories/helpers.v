From stdpp Require Import list.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import proofmode notation.

Definition CAP_CONST : nat := 10.

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

Section Inbound.
  Definition deque_bound (t b : nat) (l : list val) :=
    t ≤ b ≤ CAP_CONST ∧ length l = CAP_CONST.

  Lemma deque_bound_init l :
    length l = CAP_CONST → deque_bound 0 0 l.
  Proof.
    intros H. unfold deque_bound. repeat split; auto.
    unfold CAP_CONST. lia.
  Qed.

  Lemma deque_bound_insert t b l i v :
    deque_bound t b l → deque_bound t b (<[i:=v]> l).
  Proof. unfold deque_bound. by rewrite insert_length. Qed.

  Lemma deque_bound_extend_right t b l :
    deque_bound t b l → b < length l → deque_bound t (S b) l.
  Proof. unfold deque_bound. lia. Qed.

  Lemma deque_bound_shrink_left t b l : 
    deque_bound t b l → t < b → deque_bound (S t) b l.
  Proof. unfold deque_bound. lia. Qed.
End Inbound.

Section list.
  Context {A : Type}.
  Implicit Types l : list A.

  (* slice l i j = l[i..j-1] *)
  Definition slice l i j := take (j - i) (drop i l).

  Lemma slice_to_nil l i j : (i >= j) → slice l i j = [].
  Proof.
    unfold slice. intros H.
    replace (j-i) with 0 by lia. auto.
  Qed.

  Lemma slice_0 l j : slice l 0 j = take j l.
  Proof.
    unfold slice. rewrite drop_0.
    by replace (j - 0) with j by lia.
  Qed.

  Lemma slice_length l i j :
    i ≤ j → j ≤ length l → length (slice l i j) = j - i.
  Proof.
    unfold slice. intros H1 H2.
    rewrite take_length drop_length. lia.
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

  Lemma slice_shrink_left l i j v :
    i < j → l !! i = Some v →
    slice l i j = v :: slice l (S i) j.
  Proof.
    unfold slice. intros Hij Hi.
    replace (j - i) with (S (j - S i)) by lia.
    erewrite drop_S; eauto.
  Qed.

  Lemma take_slice l i j :
    i ≤ j ≤ length l → take j l = take i l ++ slice l i j.
  Proof.
    intros H. induction i.
    { simpl. by rewrite slice_0. }
    assert (is_Some (l !! i)) as [x Hi].
    { apply lookup_lt_is_Some. lia. }
    erewrite take_S_r; eauto.
    list_simplifier. rewrite <- slice_shrink_left; auto; try lia.
    apply IHi; lia.
  Qed.

  (* prefix *)

  Lemma take_prefix i l :
  take i l `prefix_of` l.
  Proof.
    revert i; induction l; intros.
    - by rewrite take_nil.
    - destruct i; simpl.
      + apply prefix_nil.
      + by apply prefix_cons.
  Qed.

  Lemma prefix_take l i j :
    i ≤ j → (take i l) `prefix_of` (take j l).
  Proof.
    intros H.
    destruct (decide (j ≤ length l)).
    - rewrite (take_slice l i j); auto.
      by apply prefix_app_r.
    - replace (take j l) with l. 2: rewrite take_ge; auto; try lia.
      apply take_prefix.
  Qed.
End list.
