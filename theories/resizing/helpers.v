From stdpp Require Import list.
From iris.heap_lang Require Import proofmode notation.

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

Section pred_infinite.
  Lemma pred_infinite_gname_notin (X : gset gname) :
    pred_infinite (λ x: gname, x ∉ X).
  Proof.
    eapply (pred_infinite_set (C:=gset gname)). intros X0.
    exists (fresh (X ∪ X0)). apply not_elem_of_union, is_fresh.
  Qed.
End pred_infinite.

Section neq.
  Lemma neq_symm (n m : nat) : n ≠ m ↔ m ≠ n.
  Proof. lia. Qed.
End neq.

Section modulo.
  Lemma rem_mod_eq (x y : nat) : (0 < y) → (x `rem` y)%Z = x `mod` y.
  Proof.
    intros Hpos. rewrite Z.rem_mod_nonneg; [rewrite Nat2Z.inj_mod| |]; lia.
  Qed.

  Lemma lt_mult (n a b : nat) : n*a < n*b → a < b.
  Proof. induction n; lia. Qed.

  Lemma close_mod_neq a b n :
    a < b < a+n → a `mod` n ≠ b `mod` n.
  Proof.
    intros H Hmod. assert (n ≠ 0) by lia.
    assert (Ha := PeanoNat.Nat.div_mod a n).
    assert (Hb := PeanoNat.Nat.div_mod b n).
    rewrite Ha in H; auto. rewrite Hb in H; auto.
    rewrite Hmod in H.
    assert (n*a`div`n < n*b`div`n < n*a`div`n + n) as H' by lia.
    replace (n*a`div`n + n) with (n*(a`div`n + 1)) in H' by lia.
    assert (a`div`n < b`div`n < a`div`n + 1); try lia.
    destruct H' as [H1 H2].
    apply lt_mult in H1; auto. apply lt_mult in H2; auto.
  Qed.
End modulo.

Section list.
  Context {A : Type}.
  Implicit Types l : list A.

  (* mod set/get *)

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
  
  (* slice *)

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

  Lemma circ_slice_nil l i j : i ≥ j → circ_slice l i j = [].
  Proof.
    unfold circ_slice. intros H. by replace (j-i) with 0 by lia.
  Qed.

  Lemma circ_slice_singleton l i :
    length l ≠ 0 →
    ∃ v, mod_get l i = Some v ∧ circ_slice l i (S i) = [v].
  Proof.
    intros Hl.
    destruct (mod_get_is_Some l i) as [v Hv]; auto.
    unfold circ_slice, circ_slice_d; simpl.
    replace (S i - i) with 1; try lia. rewrite Hv.
    by exists v.
  Qed.

  Lemma circ_slice_length l i j :
    length l ≠ 0 →
    length (circ_slice l i j) = j - i.
  Proof.
    unfold circ_slice. intros Hlen.
    remember (j-i) as ji eqn:Hji. revert i j Hji.
    induction ji as [|len IHji]; intros i j Hji; auto. simpl.
    destruct (mod_get_is_Some l i) as [x Hx]; auto. rewrite Hx.
    simpl. rewrite (IHji (S i) j); lia.
  Qed.

  Lemma circ_slice_split m l i j :
    length l ≠ 0 → i ≤ m ≤ j →
    circ_slice l i j = circ_slice l i m ++ circ_slice l m j.
  Proof.
    unfold circ_slice. intros Hlen Hm.
    remember (m-i) as dif eqn:Hdif. revert i m j Hm Hdif.
    induction dif as [|dif IHdif]; intros i m j Hm Hdif; simpl.
    { replace m with i; by try lia. }
    destruct (j-i) as [|ji] eqn:Eji; try lia. simpl.
    destruct (mod_get_is_Some l i) as [x Hx]; auto. rewrite Hx.
    assert (j - S i = ji) as Eji' by lia.
    specialize (IHdif (S i) m j). rewrite Eji' in IHdif.
    rewrite IHdif; auto. all: lia.
  Qed.

  Lemma circ_slice_split_eq m l l' i j :
    length l ≠ 0 → length l' ≠ 0 →
    i ≤ m ≤ j →
    circ_slice l i j = circ_slice l' i j →
    circ_slice l i m = circ_slice l' i m ∧
    circ_slice l m j = circ_slice l' m j.
  Proof.
    intros Hlen Hlen' Hm Heqs.
    rewrite (circ_slice_split m l) in Heqs; auto.
    rewrite (circ_slice_split m l') in Heqs; auto.
    apply app_inj_1 in Heqs; auto.
    do 2 (rewrite circ_slice_length; auto).
  Qed.

  Lemma circ_slice_extend_right l i j v :
    length l ≠ 0 →
    i ≤ j → mod_get l j = Some v →
    circ_slice l i (S j) = circ_slice l i j ++ [v].
  Proof.
    unfold circ_slice. intros Hlen Hij Hj.
    replace (S j - i) with (S (j - i)) by lia.
    remember (j - i) as d eqn:Heqd. revert i Hij Heqd.
    induction d as [|d IHd]; intros i Hij Heqd.
    - simpl. replace i with j by lia. by rewrite Hj.
    - assert (is_Some (mod_get l i)) as [vi Vi] by by apply mod_get_is_Some.
      simpl. rewrite Vi; simpl.
      rewrite -(IHd (S i)); try lia. auto.
  Qed.

  Lemma circ_slice_update_right l i j v :
    length l ≠ 0 →
    i ≤ j < (i + length l) →
    circ_slice (mod_set l j v) i j = circ_slice l i j.
  Proof.
    unfold circ_slice. intros Hlen Hij.
    remember (j - i) as d eqn:Heqd. revert i Hij Heqd.
    induction d as [|d IHd]; intros i Hij Heqd; auto.
    assert (i < j) by lia.
    assert (is_Some (mod_get l i)) as [vi Vi] by by apply mod_get_is_Some.
    assert (mod_get (mod_set l j v) i = Some vi) as Vi'.
    { rewrite mod_set_get_ne; auto.
      assert (i < j < i + length l) as H' by lia.
      apply (close_mod_neq _ _ (length l)) in H'. lia. }
    simpl. rewrite Vi Vi'.
    rewrite -(IHd (S i)); by try lia.
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
