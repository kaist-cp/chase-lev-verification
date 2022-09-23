From stdpp Require Import countable list.
From smr.lang Require Import notation.
From iris.algebra Require Export coPset.
From iris.prelude Require Import options.

Ltac encode_agree Hγ :=
  match type of Hγ with
  | ?γ = ?e =>
      match goal with
      | H1 : ?γ = ?e, H2 : ?γ = _ |- _ =>
          rewrite H1 in H2; apply (inj encode) in H2;
          first [ injection H2 as [= <- <- <- <- <- <- <-]
                | injection H2 as [= <- <- <- <- <- <-]
                | injection H2 as [= <- <- <- <- <-]
                | injection H2 as [= <- <- <- <-]
                | injection H2 as [= <- <- <-]
                | injection H2 as [= <- <-] ]
      end
  end.

Section list.
Local Open Scope nat.

Context {A B : Type} (f : A → B).
Implicit Types a : A.
Implicit Types b : B.
Implicit Types l : list A.

Lemma lookup_fmap_lt_Some l i b : f <$> l !! i = Some b → i < length l.
Proof. revert i. induction l; intros [|?] ?; naive_solver auto with arith. Qed.

Lemma prefix_lookup_fmap l1 l2 i b :
  f <$> l1 !! i = Some b → l1 `prefix_of` l2 → f <$> l2 !! i = Some b.
Proof. intros ? [k ->]. rewrite lookup_app_l; eauto using lookup_fmap_lt_Some. Qed.

Lemma prefix_of_reverse_cons l x :
  reverse l `prefix_of` reverse (x::l).
Proof.
  apply prefix_suffix_reverse. do 2 rewrite reverse_involutive.
  by apply suffix_cons_r.
Qed.

Lemma prefix_app_cut l1 l2 :
  l1 `prefix_of` l1 ++ l2.
Proof.
  revert l1 l2. induction l1; intros.
  - apply prefix_nil.
  - list_simplifier. by apply prefix_cons.
Qed.

Lemma take_prefix i l :
  take i l `prefix_of` l.
Proof.
  revert i; induction l; intros.
  - by rewrite take_nil.
  - destruct i; simpl.
    + apply prefix_nil.
    + by apply prefix_cons.
Qed.

Lemma head_drop i l :
  head (drop i l) = l !! i.
Proof.
  revert i; induction l; intros.
  - by rewrite drop_nil.
  - destruct i; simpl; auto.
Qed.

Lemma take_last i l :
  is_Some (l !! i) → last (take (S i) l) = l !! i.
Proof.
  revert i; induction l; intros.
  - by rewrite take_nil.
  - destruct i; simpl; auto.
    rewrite lookup_cons in H.
    rewrite last_cons.
    rewrite <- IHl.
Admitted.

(* reverse *)

Lemma rev_des l :
  l = [] ∨ ∃ x l', l = l' ++ [x].
Proof.
Admitted.

Lemma snoc_lookup x l :
  (l ++ [x]) !! length l = Some x.
Proof.
  rewrite lookup_app_r; last lia.
  replace (length l - length l) with 0 by lia. auto.
Qed.

Lemma reverse_rev l :
  reverse l = rev l.
Proof. by rewrite rev_alt. Qed.

Lemma NoDup_reverse l :
  NoDup l ↔ NoDup (reverse l).
Proof.
  assert (∀ l', NoDup l' → NoDup (reverse l')).
  { intros. apply NoDup_ListNoDup. rewrite reverse_rev.
    by apply NoDup_rev, NoDup_ListNoDup. }
  split; auto. intros.
  apply H in H0. by rewrite reverse_involutive in H0.
Qed.

Lemma notin_reverse l x :
  x ∉ l → x ∉ reverse l.
Proof. intros. intro. by rewrite elem_of_reverse in H0. Qed.

(* snoc *)

Lemma snoc_length x l :
  length (l ++ [x]) = S (length l).
Proof. rewrite app_length; simpl. lia. Qed.

Lemma NoDup_snoc x l :
  (NoDup l ∧ x ∉ l) ↔ NoDup (l ++ [x]).
Proof.
  split; intros.
  - apply NoDup_reverse. rewrite reverse_snoc.
    destruct H. apply NoDup_reverse in H. constructor; auto.
    by apply notin_reverse.
  - apply NoDup_app in H as [H1 [H2 _]]. split; auto.
    intro. apply H2 in H. by apply H, elem_of_list_singleton.
Qed.

Lemma elem_of_snoc l x y : x ∈ l ++ [y] ↔ x = y ∨ x ∈ l.
Proof.
  by rewrite -elem_of_reverse reverse_snoc
    elem_of_cons elem_of_reverse.
Qed.

End list.

Section coPset.

Lemma top_diff_union (E : coPset) :
  ⊤ = (⊤ ∖ E) ∪ E.
Proof.
  symmetry.
  rewrite [t in _ = t](union_difference_L E ⊤); set_solver.
Qed.

End coPset.
