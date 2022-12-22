From iris.algebra Require Import list excl_auth.
From refinedc.typing Require Import typing atomic_int.
From refinedc.project.ex.deque Require Import generated_code.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import invariants ghost_var mono_nat.
From refinedc.project.ex.deque Require Import mono_list helper.
From iris.prelude Require Import options.
Set Default Proof Using "Type".

(** Ghost state for the deque *)

Class dequeG Σ := DequeG {
    deque_tokG :> inG Σ (excl_authR $ listO ZO);
    deque_popG :> ghost_varG Σ bool;
    mono_listG :> mono_listG Z Σ;
    mono_natG :> mono_natG Σ
  }.

Definition dequeΣ : gFunctors :=
  #[GFunctor (excl_authR $ listO ZO);
    ghost_varΣ bool;
    mono_listΣ Z;
    mono_natΣ
  ].

Global Instance subG_dequeΣ {Σ} : subG dequeΣ Σ → dequeG Σ.
Proof. solve_inG. Qed.

(* we wrap monotonicity for easier reasoning *)
Section monotone_ghost.
  Context `{!heapGS Σ, !dequeG Σ} (N : namespace).
  Notation iProp := (iProp Σ).

  Definition mono_deque_auth_own (γm : gname) (hl : list Z) (t b : nat) : iProp :=
    ∃ (γl γt : gname),
    ⌜γm = encode (γl, γt)⌝ ∗
    ⌜(length hl = t ∧ t = b) ∨ (length hl = S t ∧ t < b)⌝ ∗
    mono_list_auth_own γl 1 hl ∗
    mono_nat_auth_own γt 1 t.

  Definition mono_deque_lb_own (γm : gname) (hl : list Z) (t b : nat) : iProp :=
    ∃ (γl γt : gname),
    ⌜γm = encode (γl, γt)⌝ ∗
    ⌜(length hl = t ∧ t = b) ∨ (length hl = S t ∧ t < b)⌝ ∗
    mono_list_lb_own γl hl ∗
    mono_nat_lb_own γt t.

  Lemma mono_deque_own_alloc v :
    ⊢ |==> ∃ γ, mono_deque_auth_own γ [v] 1 1.
  Proof.
    iMod (mono_list_own_alloc [v]) as (γl) "[L _]".
    iMod (mono_nat_own_alloc 1) as (γtb) "[N _]".
    iExists (encode (γl, γtb)). iModIntro.
    iExists _,_. iSplit; iFrame; auto.
  Qed.

  Lemma mono_deque_auth_history γm l t b :
    mono_deque_auth_own γm l t b -∗
    ⌜(length l = t ∧ t = b) ∨ (length l = S t ∧ t < b)⌝.
  Proof. iIntros "(%γl & %γt & %ENC & %BOUND & L & N)". auto. Qed.

  Lemma mono_deque_lb_history γm l t b :
    mono_deque_lb_own γm l t b -∗
    ⌜(length l = t ∧ t = b) ∨ (length l = S t ∧ t < b)⌝.
  Proof. iIntros "(%γl & %γt & %ENC & %BOUND & L & N)". auto. Qed.

  Lemma mono_deque_lb_lookup γm i l1 t1 b1 l2 t2 b2 :
    i < length l1 → i < length l2 →
    mono_deque_lb_own γm l1 t1 b1 -∗ mono_deque_lb_own γm l2 t2 b2 -∗
    ⌜l1 !! i = l2 !! i⌝.
  Proof.
    iIntros (Hi Hv).
    iIntros "(%γl & %γt & %ENC1 & %BOUND1 & L1 & N1)".
    iIntros "(%γl' & %γt' & %ENC2 & %BOUND2 & L2 & N2)".
      encode_agree ENC1.
    assert (is_Some (l1 !! i)) as [v1 Hv1] by (rewrite lookup_lt_is_Some; auto).
    assert (is_Some (l2 !! i)) as [v2 Hv2] by (rewrite lookup_lt_is_Some; auto).
    iDestruct (mono_list_lb_valid with "L1 L2") as "%Pref".
    destruct Pref.
    - rewrite Hv1. erewrite prefix_lookup; eauto.
    - rewrite Hv2. erewrite prefix_lookup; eauto.
  Qed.

  Lemma mono_deque_get_lb γm l t b :
    mono_deque_auth_own γm l t b -∗
    mono_deque_lb_own γm l t b.
  Proof.
    iIntros "(%γl & %γt & %ENC & %BOUND & L & N)".
    iDestruct (mono_list_lb_own_get with "L") as "#Llb".
    iDestruct (mono_nat_lb_own_get with "N") as "#Nlb".
    iExists _,_. repeat iSplit; auto.
  Qed.

  Lemma mono_deque_auth_lb_length γm l1 t1 b1 l2 t2 b2 :
    mono_deque_auth_own γm l1 t1 b1 -∗ mono_deque_lb_own γm l2 t2 b2 -∗
    ⌜length l2 ≤ length l1⌝.
  Proof.
    iIntros "(%γl & %γt & %ENC1 & %BOUND1 & L1 & N1)".
    iIntros "(%γl' & %γt' & %ENC2 & %BOUND2 & L2 & N2)".
      encode_agree ENC1.
    iDestruct (mono_list_auth_lb_valid with "L1 L2") as "[_ %Pref]".
    by apply prefix_length in Pref.
  Qed.

  Lemma mono_deque_auth_lb_top γm l1 t1 b1 l2 t2 b2 :
    mono_deque_auth_own γm l1 t1 b1 -∗ mono_deque_lb_own γm l2 t2 b2 -∗
    ⌜t2 ≤ t1 ∧ (t1 = t2 → t2 < b2 → t1 < b1)⌝.
  Proof.
    iIntros "D1 D2".
    iDestruct (mono_deque_auth_lb_length with "D1 D2") as "%D".
    iDestruct "D1" as "(%γl & %γt & %ENC1 & %BOUND1 & L1 & N1)".
    iDestruct "D2" as "(%γl' & %γt' & %ENC2 & %BOUND2 & L2 & N2)".
      encode_agree ENC1.
    iDestruct (mono_nat_lb_own_valid with "N1 N2") as "[_ %Le]".
    iPureIntro. lia.
  Qed.

  Lemma mono_deque_steal γm v l t b :
    t < b →
    mono_deque_auth_own γm l t b ==∗
    mono_deque_auth_own γm
      (if decide (S t = b) then l else l ++ [v])
      (S t) b.
  Proof.
    iIntros (H) "(%γl & %γt & %ENC & %BOUND & L & N)".
    destruct BOUND; try lia.
    iMod (mono_nat_own_update (S t) with "N") as "[N _]". 1: lia.
    case_decide.
    - iModIntro. iExists _,_. repeat iSplit; auto; iFrame.
      iPureIntro. lia.
    - iMod (mono_list_auth_own_update (l ++ [v]) with "L") as "[L _]".
      1: by apply prefix_app_r.
      iModIntro. iExists _,_. repeat iSplit; auto; iFrame.
      iPureIntro. right. split; try lia.
      rewrite app_length; simpl. lia.
  Qed.

  Lemma mono_deque_pop_singleton γm l t :
    mono_deque_auth_own γm l t (S t) ==∗
    mono_deque_auth_own γm l (S t) (S t).
  Proof.
    iIntros "D".
    iMod (mono_deque_steal _ 0 with "D"). 1: lia.
    case_decide; auto. by destruct H.
  Qed.

  Lemma mono_deque_push γm l2 b2 l1 t b1 :
    b1 < b2 →
    ((t = b1 ∧ ∃ v, l2 = l1 ++ [v]) ∨
      (t < b1 ∧ l1 = l2)
    ) →
    mono_deque_auth_own γm l1 t b1 ==∗ mono_deque_auth_own γm l2 t b2.
  Proof.
    iIntros (H HU) "(%γl & %γt & %ENC & %BOUND & L & N)".
    destruct HU as [[Ht [v Hl]] | [Ht Hl]];
    destruct BOUND as [[Hl1 Hb] | [Hl1 Hb]]; try lia; subst.
    - iMod (mono_list_auth_own_update (l1 ++ [v]) with "L") as "[L _]".
      { by apply prefix_app_r. }
      iModIntro. iExists _,_. repeat iSplit; auto; iFrame.
      iPureIntro. right; split; auto. rewrite app_length; simpl. lia.
    - iModIntro. iExists _,_. repeat iSplit; auto; iFrame.
      iPureIntro. right; split; auto. lia.
  Qed.

  Lemma mono_deque_pop γm b2 l t b1 :
    t < b1 → t < b2 →
    mono_deque_auth_own γm l t b1 -∗ mono_deque_auth_own γm l t b2.
  Proof.
    iIntros (H1 H2) "(%γl & %γt & %ENC & %BOUND & L & N)".
    destruct BOUND as [[Hl1 Hb] | [Hl1 Hb]]; try lia.
    iExists _,_. repeat iSplit; auto; iFrame.
  Qed.
End monotone_ghost.


Section type.
  Context `{!typeG Σ} `{!dequeG Σ}.
  Notation iProp := (iProp Σ).

  Global Instance inv_own_constraint (N : namespace) (P : iProp):
    OwnConstraint (λ β, match β return _ with Own => P | Shr => inv N P end).
  Proof.
    constructor; first apply _.
    iIntros (??) "H". by iMod (inv_alloc with "H").
  Qed.

  Definition with_invariant (ty : type) (N : namespace) (P : iProp) : type :=
    own_constrained (λ β, match β return _ with Own => P | Shr => inv N P end) ty.

  Fixpoint array_half (p : loc) (l : list Z) : iProp :=
    match l with
    | [] => True%I
    | v::l' => p ↦{1/2} (i2v v i32) ∗ array_half (p +ₗ 1) l'
    end.

  Definition deque_inv (g : gname) (arr sz top bot : loc) : iProp :=
    ∃ (γq γpop γm : gname) (n t b : nat) (l : list Z) (Popping : bool),
      ⌜g = encode (γq, γpop, γm)⌝ ∗
      ⌜1 ≤ t ≤ b ∧ length l = n ∧ n > 0⌝ ∗
      (* physical data *)
      ( let bp := if Popping then b-1 else b in
        array_half arr l ∗
        sz ◁ₗ n @ int i32 ∗
        top ◁ₗ t @ int i32 ∗
        bot ↦{1/2} (i2v (Z.of_nat bp) i32)
      ) ∗
      (* logical data *)
      ( own γq (●E (circ_slice l t b)) ∗
        ghost_var γpop (1/2) Popping
      ) ∗
      (* history of determined elements *)
      ( ∃ (hl : list Z),
        mono_deque_auth_own γm hl t b ∗
        ⌜t < b → hl !! t = mod_get l t⌝
      ).

(*
  Global Instance hyp_spinlock_t_timeless g a s t b: Timeless (hyp_spinlock_t_invariant g a s t b).
  Proof. rewrite /hyp_spinlock_t_invariant /ty_own /=. apply _. Qed.
*)

  Definition own_deque (γ : gname) (n : nat) (q : loc) : iProp :=
    ∃ (γq γpop γm : gname) (sz arr top bot : loc) (b : nat) (l : list Z),
      ⌜γ = encode (γq, γpop, γm)⌝ ∗
      q ◁ₗ{Shr} struct struct_deque [ place arr ; place sz ; place top ; place bot ] ∗
      ⌜length l = n⌝ ∗
      ghost_var γpop (1/2) false ∗
      array_half arr l ∗
      bot ↦{1/2} (i2v (Z.of_nat b) i32).
  
  Definition deque_content (γ : gname) (frag : list Z) : iProp :=
    ∃ (γq γpop γm : gname),
      ⌜γ = encode (γq, γpop, γm)⌝ ∗
      own γq (◯E frag).

  Definition dequeN : namespace := nroot.
  Definition deque (g : gname) : type :=
    tyexists (λ arr, tyexists (λ sz, tyexists (λ top, tyexists (λ bot,
      with_invariant (
        struct struct_deque [ place arr ; place sz ; place top ; place bot ]
      ) dequeN (deque_inv g sz arr top bot)
    )))).

End type.
