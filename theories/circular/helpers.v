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

Section nat.
  Lemma neq_symm (x y : nat) : x ≠ y → y ≠ x.
  Proof. lia. Qed.

  Lemma lt_mult (n a b : nat) : n ≠ 0 → n*a < n*b → a < b.
  Proof. intros. induction n; lia. Qed.
End nat.

Section modulo.
  Lemma rem_mod_eq (x y : nat) : (0 < y) → (x `rem` y)%Z = x `mod` y.
  Proof.
    intros Hpos. rewrite Z.rem_mod_nonneg; [rewrite Nat2Z.inj_mod| |]; lia.
  Qed.

  Lemma mod_neq a b n :
    a < b < a+n → a `mod` n ≠ b `mod` n.
  Proof.
    intros H amn. assert (n ≠ 0). 1: lia.
    assert (Ha := PeanoNat.Nat.div_mod a n).
    assert (Hb := PeanoNat.Nat.div_mod b n).
    rewrite Ha in H; auto. rewrite Hb in H; auto.
    rewrite amn in H.
    assert (n*a`div`n < n*b`div`n < n*a`div`n + n) by lia.
    replace (n*a`div`n + n) with (n*(a`div`n + 1)) in H1 by lia.
    assert (a`div`n < b`div`n < a`div`n + 1); try lia.
    destruct H1 as [H1A H1B].
    apply lt_mult in H1A; auto. apply lt_mult in H1B; auto.
  Qed.

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
End list.
