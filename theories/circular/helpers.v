From stdpp Require Import list.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import proofmode notation.

Definition CAP_CONST : nat := 20.

Ltac encode_agree Hγ :=
  match type of Hγ with
  | ?γ = ?e =>
      match goal with
      | H1 : ?γ = ?e, H2 : ?γ = _ |- _ =>
          rewrite H1 in H2; apply (inj encode) in H2;
          first [ injection H2 as [= <- <- <- <- <- <- <- <- <- <- <-]
                | injection H2 as [= <- <- <- <- <- <- <- <- <- <-]
                | injection H2 as [= <- <- <- <- <- <- <- <- <-]
                | injection H2 as [= <- <- <- <- <- <- <- <-]
                | injection H2 as [= <- <- <- <- <- <- <-]
                | injection H2 as [= <- <- <- <- <- <-]
                | injection H2 as [= <- <- <- <- <-]
                | injection H2 as [= <- <- <- <-]
                | injection H2 as [= <- <- <-]
                | injection H2 as [= <- <-] ]
      end
  end.

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

Section modulo.
  Lemma rem_mod_eq (x y : nat) : (0 < y) → (x `rem` y)%Z = x `mod` y.
  Proof.
    intros Hpos. rewrite Z.rem_mod_nonneg; [rewrite Nat2Z.inj_mod| |]; lia.
  Qed.

  Lemma mod_neq a b n :
    a < b < a+n → a `mod` n ≠ b `mod` n.
  Proof. Admitted.

  Context {A : Type}.
  Implicit Types l : list A.
  Definition mod_set l i v := <[i `mod` length l:=v]> l.
  Definition mod_get l i := l !! (i `mod` length l).

  Lemma mod_get_is_Some l i :
    length l ≠ 0 → is_Some (mod_get l i).
  Proof. intros H. by apply lookup_lt_is_Some, Nat.mod_upper_bound. Qed.

  Lemma mod_set_length l i v : length (mod_set l i v) = length l.
  Proof. by rewrite insert_length. Qed.

  Lemma mod_set_get l i j v :
    length l ≠ 0 →
    i `mod` length l = j `mod` length l →
    mod_get (mod_set l i v) j = Some v.
  Proof.
    intros H Hij. unfold mod_get, mod_set.
    rewrite insert_length Hij list_lookup_insert; auto.
    by apply Nat.mod_upper_bound.
  Qed.

  Lemma mod_set_get_ne l i j v :
    i `mod` length l ≠ j `mod` length l →
    mod_get (mod_set l i v) j = mod_get l j.
  Proof.
    intros Hij. unfold mod_get, mod_set.
    by rewrite insert_length list_lookup_insert_ne.
  Qed.
End modulo.

Section list.
  Context {A : Type}.
  Implicit Types l : list A.

  (* circ_slice l i j = l[i%len..(j-1)%len] *)
  Fixpoint circ_slice_d l i d :=
    match d with
    | O => []
    | S d' => match mod_get l i with
      | Some v => v :: circ_slice_d l (S i) d'
      | None => []
      end
    end.
  Definition circ_slice l i j := circ_slice_d l i (j-i).

  Lemma circ_slice_to_nil l i j : i ≥ j → circ_slice l i j = [].
  Proof.
    unfold circ_slice. intros H. by replace (j-i) with 0 by lia.
  Qed.
(*
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
*)
  Lemma circ_slice_extend_right l i j v :
    length l ≠ 0 →
    i ≤ j → mod_get l j = Some v →
    circ_slice l i (S j) = circ_slice l i j ++ [v].
  Proof.
    unfold circ_slice. intros Hlen Hij Hj.
    replace (S j - i) with (S (j - i)) by lia.
    remember (j - i) as d. revert i Hij Heqd.
    induction d; intros.
    - simpl. replace i with j by lia. by rewrite Hj.
    - assert (is_Some (mod_get l i)) as [vi Vi]. 1: by apply mod_get_is_Some.
      simpl. rewrite Vi. simpl.
      rewrite <- (IHd (S i)); try lia. auto.
  Qed.

  Lemma circ_slice_update_right l i j v :
    length l ≠ 0 →
    i ≤ j < (i + length l) →
    circ_slice (mod_set l j v) i j = circ_slice l i j.
  Proof.
    unfold circ_slice. intros Hlen Hij.
    remember (j - i) as d. revert i Hij Heqd.
    induction d; intros; auto.
    assert (i < j) by lia.
    assert (is_Some (mod_get l i)) as [vi Vi]. 1: by apply mod_get_is_Some.
    assert (mod_get (mod_set l j v) i = Some vi) as Vi'.
    { rewrite mod_set_get_ne; auto. assert (i < j < i + length l) by lia.
      apply (mod_neq _ _ (length l)) in H0. lia. }
    simpl. rewrite Vi Vi'.
    rewrite <- (IHd (S i)); try lia. auto.
  Qed.

  Lemma circ_slice_shrink_right l i j v :
    length l ≠ 0 →
    i < j → mod_get l (j - 1) = Some v →
    circ_slice l i j = circ_slice l i (j - 1) ++ [v].
  Proof.
    intros. replace j with (S (j - 1)) by lia.
    erewrite circ_slice_extend_right; eauto; try lia.
    by replace (S (j - 1)) with j by lia.
  Qed.

  Lemma circ_slice_shrink_left l i j v :
    length l ≠ 0 →
    i < j → mod_get l i = Some v →
    circ_slice l i j = v :: circ_slice l (S i) j.
  Proof.
    unfold circ_slice. intros H Hij Hi.
    replace (j - i) with (S (j - S i)) by lia. simpl.
    by rewrite Hi.
  Qed.

  (* prefix *)
(*
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
*)
  Lemma reverse_equal l1 l2 :
    reverse l1 = reverse l2 → l1 = l2.
  Proof.
    intros.
    rewrite <- (reverse_involutive l1).
    rewrite <- (reverse_involutive l2). by rewrite H.
  Qed.

  Lemma snoc_equal l1 l2 x y :
    l1 ++ [x] = l2 ++ [y] → l1 = l2.
  Proof.
    intros.
    rewrite <- (reverse_involutive (l1 ++ [x])) in H.
    rewrite <- (reverse_involutive (l2 ++ [y])) in H.
    do 2 rewrite reverse_snoc in H.
    apply reverse_equal in H.
    injection H; intros. by apply reverse_equal.
  Qed.

  Lemma prefix_app_same_prefix l1 l2 l3 :
    l1 `prefix_of` l2 ++ l3 → length l1 = length l2 →
    l1 = l2.
  Proof.
    unfold prefix.
    induction l3 using rev_ind; intros [k H] Hl.
    - rewrite app_nil_r in H. subst. rewrite app_length in Hl.
      destruct k.
      + by rewrite app_nil_r.
      + simpl in Hl. lia.
    - apply IHl3; auto.
      destruct k using rev_ind.
      + rewrite app_nil_r in H. subst.
        do 2 rewrite app_length in Hl. simpl in Hl. lia.
      + exists k. do 2 rewrite app_assoc in H.
        by apply snoc_equal in H.
  Qed.
End list.
