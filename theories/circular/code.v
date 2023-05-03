From iris.algebra Require Import list excl_auth mono_nat.
From iris.bi Require Import derived_laws_later.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import invariants ghost_var ghost_map.
From chase_lev Require Import mono_nat atomic.
From iris.heap_lang Require Import proofmode notation.
From iris.prelude Require Import options.
From chase_lev.circular Require Import helpers spec.

(*
We use a finite length circular list without resizing.
if the array is full, the push function tries again.

19    0  1  2  3  4  5     6
  +--+--+--+--+--+--+--+--+
  |99|10|20|30|40|04|05|06|
  +--+--+--+--+--+--+--+--+
18|88|   ^        ^    |07|7
  +--+   top      bot  +--+
17|77|                 |08|8
  +--+--+--+--+--+--+--+--+
  |66|55|44|33|22|11|10|09|
  +--+--+--+--+--+--+--+--+
16    15 14 13 12 11 10    9

This deque has the following physical state:
- t = 21, b = 24
- l = [10, 20, ..., 99]

and the following abstract state:
- t = 21, b = 24, "not popping"
- content = [20, 30, 40]
- history = [_, 1, 2, ..., 10, 11, ..., 99, 10, 20]
    where 1 to 3 were erased from the array     ^
                                                t
Note on history:
- history is the list of "determined elements", i.e.
  those that are definitely the last element pushed at
  each index and won't be overwritten.
- history includes indices from 0 to either t or t-1.
  If t = b, the element at t may be overwritten by push,
  so history goes up to t-1. Otherwise, it goes up to t.
- history[0] does not correspond to any element in l
  since t starts from 1 (because we need to decrement b).
  As such, it can be any value.
*)

Local Ltac extended_auto :=
  eauto;
  try rewrite Nat2Z.id;
  try rewrite replicate_length;
  try rewrite mod_set_length;
  try rewrite Qp.half_half;
  try by (
    repeat iNext; repeat iIntros; repeat intros;
    try case_decide; try iPureIntro;
    try rewrite lookup_lt_is_Some;
    try lia; done
  ).
Local Ltac fr :=
  repeat iIntros; repeat iSplit; extended_auto;
  repeat iIntros; repeat iExists _;
  try iFrame "arr↦"; try iFrame "arr↦1"; try iFrame "arr↦2"; 
  iFrame; eauto.

Section code.
  Definition new_deque : val :=
    λ: "sz",
      let: "array" := AllocN "sz" #0 in
      ("sz", "array", ref #1, ref #1). (* size, array, top, bottom *)
  
  Definition sz : val := λ: "deque", Fst (Fst (Fst "deque")).
  Definition arr : val := λ: "deque", Snd (Fst (Fst "deque")).
  Definition top : val := λ: "deque", Snd (Fst "deque").
  Definition bot : val := λ: "deque", Snd "deque".

  Definition push : val :=
    rec: "push" "deque" "v" :=
      let: "sz" := sz "deque" in
      let: "array" := arr "deque" in
      let: "b" := !(bot "deque") in
      if: !(top "deque") + "sz" ≤ "b" + #1
        then "push" "deque" "v"
      else
      "array" +ₗ ("b" `rem` "sz") <- "v" ;;
      bot "deque" <- "b" + #1.
  
  Definition pop : val :=
    λ: "deque",
      let: "sz" := sz "deque" in
      let: "array" := arr "deque" in
      let: "b" := !(bot "deque") - #1 in
      bot "deque" <- "b" ;;
      let: "t" := !(top "deque") in
      if: "b" < "t" then (* empty pop *)
        bot "deque" <- "t" ;; NONE
      else let: "v" := !("array" +ₗ ("b" `rem` "sz")) in
      if: "t" < "b" then SOME "v" (* normal case *)
      else let: "ok" := CAS (top "deque") "t" ("t" + #1) in
      bot "deque" <- "t" + #1 ;;
      if: "ok" then SOME "v" (* popped *)
      else NONE. (* stolen *)

  (* NOTE: b ≤ t doesn't necessarily mean the deque was empty!
    It can also be the case that there was one element and
    the owner thread decremented b trying to pop. *)
  Definition steal : val :=
    λ: "deque",
      let: "sz" := sz "deque" in
      let: "array" := arr "deque" in
      let: "t" := !(top "deque") in
      let: "b" := !(bot "deque") in
      if: "b" ≤ "t" then NONE (* no chance *)
      else let: "v" := !("array" +ₗ ("t" `rem` "sz")) in
      if: CAS (top "deque") "t" ("t" + #1)
      then SOME "v" (* success *)
      else NONE. (* fail *)
End code.

(** Ghost state for the deque *)

Class dequeG Σ := DequeG {
    (* spec *)
    deque_tokG :> inG Σ (excl_authR $ listO valO);
    (* info: arr, bot, popping *)
    deque_infoG :> ghost_varG Σ (list val * nat * bool);
    (* RA *)
    topbotG :> mono_natG Σ;
    topeltG :> ghost_mapG Σ nat (option val)
  }.

Definition dequeΣ : gFunctors :=
  #[ (*invariant *)
    GFunctor (excl_authR $ listO valO);
    ghost_varΣ (list val * nat * bool);
    (* RA *)
    mono_natΣ;
    ghost_mapΣ nat (option val)
  ].

Global Instance subG_dequeΣ {Σ} : subG dequeΣ Σ → dequeG Σ.
Proof. solve_inG. Qed.

Section dqst.
  Context `{!heapGS Σ, !dequeG Σ}.
  Notation iProp := (iProp Σ).
  Definition dqst_gnames : Type := gname*gname.

  Definition top_bot_state (t b : nat) : nat :=
    2*t + (if bool_decide (t < b) then 1 else 0).

  Definition dqst_frag (γdqst : dqst_gnames) (l : list val) (t b : nat) : iProp :=
    let (γtb, γelt) := γdqst in
    ⌜1 ≤ t ≤ b ∧ b < t + length l ∧ length l ≠ 0⌝ ∗
    (* top-bot profile *)
    mono_nat_lb_own γtb (top_bot_state t b) ∗
    (* top element preservation *)
    if (bool_decide (t = b)) then True%I else (t ↪[γelt]□ (mod_get l t))%I.

  Definition dqst_auth (γdqst : dqst_gnames) (l : list val) (t b : nat) : iProp :=
    let (γtb, γelt) := γdqst in
    ⌜1 ≤ t ≤ b ∧ b < t + length l ∧ length l ≠ 0⌝ ∗
    (* top-bot profile *)
    mono_nat_auth_own γtb 1 (top_bot_state t b) ∗
    (* top element preservation *)
    ( ∃ (elts : gmap nat (option val)),
      ghost_map_auth γelt 1 elts ∗
      (if (bool_decide (t = b)) then True%I else (t ↪[γelt]□ (mod_get l t))%I) ∗
      ⌜∀ (n : nat), n ≥ t + (if bool_decide (t = b) then 0 else 1) → elts !! n = None⌝
    ).

  (* Timeless & Persistent *)
  Ltac desγ H :=
    destruct H as (γtb, γelt).

  Global Instance dqst_frag_timeless γdqst l t b :
    Timeless (dqst_frag γdqst l t b).
  Proof. desγ γdqst. unfold dqst_frag. case_bool_decide; apply _. Qed.

  Global Instance dqst_frag_persistent γdqst l t b :
    Persistent (dqst_frag γdqst l t b).
  Proof. desγ γdqst. unfold dqst_frag. case_bool_decide; apply _. Qed.

  Global Instance dqst_auth_timeless γdqst l t b :
    Timeless (dqst_auth γdqst l t b).
  Proof. desγ γdqst. unfold dqst_auth. case_bool_decide; apply _. Qed.

  Lemma top_bot_state_le t1 b1 t2 b2 :
    top_bot_state t1 b1 ≤ top_bot_state t2 b2 ↔
    t1 ≤ t2 ∧ (t1 = t2 ∧ t1 < b1 → t2 < b2).
  Proof. unfold top_bot_state. do 2 case_bool_decide; lia. Qed.

  Lemma dqst_auth_alloc l :
    length l ≠ 0 →
    ⊢ |==> ∃ (γdqst : dqst_gnames),
      dqst_auth γdqst l 1 1.
  Proof.
    intros Hl. unfold dqst_auth.
    iMod (mono_nat_own_alloc 2) as (γtb) "[tb _]".
    iMod (ghost_map_alloc (∅ : gmap nat (option val))) as (γelt) "[topelt _]".
    iExists (γtb, γelt). iModIntro. fr.
  Qed.
(*
  Lemma dqst_frag_agree γdqst l1 t1 b1 l2 t2 b2 :
    dqst_frag γdqst l1 t1 b1 -∗
    dqst_frag γdqst l2 t2 b2 -∗
    ⌜length l1 = length l2⌝.
  Proof.
    desγ γdqst.
    iIntros "F1 F2".
      iDestruct "F1" as "(%Hlt1 & tb1 & elt1)".
      iDestruct "F2" as "(%Hlt2 & tb2 & elt2)".
    iDestruct (ghost_map_elem_agree with "muse1 muse2") as "%Eqera".
    injection Eqera; fr.
  Qed.

  Lemma dqst_lb_lookup γm i l1 t1 b1 l2 t2 b2 :
    i < length l1 → i < length l2 →
    dqst_frag γm l1 t1 b1 -∗ dqst_frag γm l2 t2 b2 -∗
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

  Lemma dqst_get_lb γm l t b :
    dqst_auth γm l t b -∗
    dqst_frag γm l t b.
  Proof.
    iIntros "(%γl & %γt & %ENC & %BOUND & L & N)".
    iDestruct (mono_list_lb_own_get with "L") as "#Llb".
    iDestruct (mono_nat_lb_own_get with "N") as "#Nlb".
    iExists _,_. repeat iSplit; auto.
  Qed.

  Lemma dqst_auth_lb_length γm l1 t1 b1 l2 t2 b2 :
    dqst_auth γm l1 t1 b1 -∗ dqst_frag γm l2 t2 b2 -∗
    ⌜length l2 ≤ length l1⌝.
  Proof.
    iIntros "(%γl & %γt & %ENC1 & %BOUND1 & L1 & N1)".
    iIntros "(%γl' & %γt' & %ENC2 & %BOUND2 & L2 & N2)".
      encode_agree ENC1.
    iDestruct (mono_list_auth_lb_valid with "L1 L2") as "[_ %Pref]".
    by apply prefix_length in Pref.
  Qed.

  Lemma dqst_auth_lb_top γm l1 t1 b1 l2 t2 b2 :
    dqst_auth γm l1 t1 b1 -∗ dqst_frag γm l2 t2 b2 -∗
    ⌜t2 ≤ t1 ∧ (t1 = t2 → t2 < b2 → t1 < b1)⌝.
  Proof.
    iIntros "D1 D2".
    iDestruct (dqst_auth_lb_length with "D1 D2") as "%D".
    iDestruct "D1" as "(%γl & %γt & %ENC1 & %BOUND1 & L1 & N1)".
    iDestruct "D2" as "(%γl' & %γt' & %ENC2 & %BOUND2 & L2 & N2)".
      encode_agree ENC1.
    iDestruct (mono_nat_lb_own_valid with "N1 N2") as "[_ %Le]".
    iPureIntro. lia.
  Qed.

  Lemma dqst_steal γm v l t b :
    t < b →
    dqst_auth γm l t b ==∗
    dqst_auth γm
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

  Lemma dqst_pop_singleton γm l t :
    dqst_auth γm l t (S t) ==∗
    dqst_auth γm l (S t) (S t).
  Proof.
    iIntros "D".
    iMod (dqst_steal _ #() with "D"). 1: lia.
    case_decide; auto. by destruct H.
  Qed.

  Lemma dqst_push γm l2 b2 l1 t b1 :
    b1 < b2 →
    ((t = b1 ∧ ∃ v, l2 = l1 ++ [v]) ∨
      (t < b1 ∧ l1 = l2)
    ) →
    dqst_auth γm l1 t b1 ==∗ dqst_auth γm l2 t b2.
  Proof.
    iIntros (H HU) "(%γl & %γt & %ENC & %BOUND & L & N)".
    destruct HU as [[Ht [v Hl]]|[Ht Hl]];
    destruct BOUND as [[Hl1 Hb]|[Hl1 Hb]]; try lia; subst.
    - iMod (mono_list_auth_own_update (l1 ++ [v]) with "L") as "[L _]".
      { by apply prefix_app_r. }
      iModIntro. iExists _,_. repeat iSplit; auto; iFrame.
      iPureIntro. right; split; auto. rewrite app_length; simpl. lia.
    - iModIntro. iExists _,_. repeat iSplit; auto; iFrame.
      iPureIntro. right; split; auto. lia.
  Qed.

  Lemma dqst_pop γm b2 l t b1 :
    t < b1 → t < b2 →
    dqst_auth γm l t b1 -∗ dqst_auth γm l t b2.
  Proof.
    iIntros (H1 H2) "(%γl & %γt & %ENC & %BOUND & L & N)".
    destruct BOUND as [[Hl1 Hb]|[Hl1 Hb]]; try lia.
    iExists _,_. repeat iSplit; auto; iFrame.
  Qed.
*)
  Lemma dqst_get_frag γdqst l t b :
    dqst_auth γdqst l t b -∗ dqst_frag γdqst l t b.
  Proof with extended_auto.
    desγ γdqst.
    iIntros "Auth".
      iDestruct "Auth" as "(%HltO & tbO & eltO)".
      iDestruct "eltO" as (elts) "(Elt & top↪ & %Heltslen)".
    iDestruct (mono_nat_lb_own_get with "tbO") as "lb". fr.
  Qed.

  Lemma dqst_get_lb γdqst l1 t1 b1 l2 t2 b2 :
    (* era1 is later than era2 *)
    dqst_auth γdqst l1 t1 b1 -∗
    dqst_frag γdqst l2 t2 b2 -∗
    ⌜t2 ≤ t1 ∧ (
      (t2 = t1 ∧ t2 < b2) →
      (t1 < b1 ∧ mod_get l2 t2 = mod_get l1 t1)
    )⌝.
  Proof with extended_auto.
    desγ γdqst.
    iIntros "Auth F".
      iDestruct "Auth" as "(%HltO & tbO & eltO)".
      iDestruct "F" as "(%Hlt & tb & elt)".
    iDestruct (mono_nat_lb_own_valid with "tbO tb") as "[_ %Htb]".
      apply top_bot_state_le in Htb as [Ht21 Htb21]. fr.
    iIntros ([H1 Ht1b2]). subst t2. assert (t1 < b1) as Htb1... fr.
    iDestruct "eltO" as (elts) "(Elt & top↪ & %Heltslen)". do 2 case_bool_decide...
    iDestruct (ghost_map_elem_agree with "elt top↪") as "%"...
  Qed.

  Lemma dqst_auth_write_bot v γdqst l t b :
    dqst_auth γdqst l t b -∗
    dqst_auth γdqst (mod_set l b v) t b.
  Proof.
    desγ γdqst.
    iIntros "Auth".
      iDestruct "Auth" as "(%HltO & tbO & eltO)".
    unfold dqst_auth. rewrite mod_set_length. case_bool_decide; fr.
    rewrite mod_set_get_ne. 1: fr. (*apply neq_symm, close_mod_neq; lia.*)
  Admitted.

  Lemma dqst_auth_push γdqst l t b :
    S b < t + length l →
    dqst_auth γdqst l t b ==∗
    dqst_auth γdqst l t (S b).
  Proof with extended_auto.
    desγ γdqst.
    iIntros (Hlt) "Auth".
      iDestruct "Auth" as "(%HltO & tbO & eltO)".
      iDestruct "eltO" as (elts) "(Elts & top↪ & %Heltslen)".
    iMod (mono_nat_own_update (top_bot_state t (S b)) with "tbO") as "[tbO _]".
    { unfold top_bot_state. do 2 case_bool_decide... }

    case_bool_decide; last first.
    { iModIntro. fr. fr. case_bool_decide... }
    iMod (ghost_map_insert t (mod_get l t) with "[Elts]") as "[Elts ntop↪]"...
      1: apply Heltslen...
      iMod (ghost_map_elem_persist with "ntop↪") as "#ntop↪".
    iModIntro. fr. fr. case_bool_decide... fr.
    iPureIntro. intros m Hm. apply lookup_insert_None. split... apply Heltslen...
  Qed.

  Lemma dqst_auth_pop γdqst l t b :
    t < b - 1 →
    dqst_auth γdqst l t b ==∗
    dqst_auth γdqst l t (b - 1).
  Proof with extended_auto.
    desγ γdqst.
    iIntros (Hlt) "Auth".
      iDestruct "Auth" as "(%HltO & tbO & eltO)".
      iDestruct "eltO" as (elts) "(Elts & top↪ & %Heltslen)".
    replace (top_bot_state t b) with (top_bot_state t (b-1)).
      2: unfold top_bot_state; repeat case_bool_decide...
    iModIntro. fr. fr. case_bool_decide... fr.
  Qed.
End dqst.

Section proof.
  Context `{!heapGS Σ, !dequeG Σ} (N : namespace).
  Notation iProp := (iProp Σ).

  Definition deque_inv (γq γsw : gname) (γdqst : dqst_gnames)
  (arr top bot : loc) : iProp :=
    ∃ (l : list val) (t b : nat) (pop : bool),
      ⌜1 ≤ t ≤ b ∧ b < t + length l ∧ length l ≠ 0⌝ ∗
      (* abstract *)
      own γq (●E (circ_slice l t b)) ∗
      ghost_var γsw (1/2) (l, b, pop) ∗
      dqst_auth γdqst l t b ∗
      (* physical *)
      arr ↦∗{#1/2} l ∗
      top ↦ #t ∗
      bot ↦{#1/2} #(if pop then b-1 else b).

  Definition is_deque (γ : gname) (q : val) : iProp :=
    ∃ (γq γsw : gname) (γdqst : dqst_gnames) (n : nat) (arr top bot : loc),
      ⌜q = (#n, #arr, #top, #bot)%V⌝ ∗
      ⌜γ = encode (γq, γsw, γdqst)⌝ ∗
      inv N (deque_inv γq γsw γdqst arr top bot).
  Global Instance is_deque_persistent γ q :
    Persistent (is_deque γ q) := _.

  Definition deque_content (γ : gname) (frag : list val) : iProp :=
    ∃ (γq γsw : gname) (γdqst : dqst_gnames),
      ⌜γ = encode (γq, γsw, γdqst)⌝ ∗
      own γq (◯E frag).
  Global Instance deque_content_timeless γ frag :
    Timeless (deque_content γ frag) := _.

  (* owner of the deque who can call push and pop *)
  Definition own_deque (γ : gname) (q : val) : iProp :=
    ∃ (γq γsw : gname) (γdqst : dqst_gnames)
    (l : list val) (arr top bot : loc) (b : nat),
      ⌜γ = encode (γq, γsw, γdqst)⌝ ∗
      ⌜q = (#(length l), #arr, #top, #bot)%V⌝ ∗
      ghost_var γsw (1/2) (l, b, false) ∗
      arr ↦∗{#1/2} l ∗
      bot ↦{#1/2} #b.
  
  Lemma deque_content_exclusive γ frag1 frag2 :
    deque_content γ frag1 -∗ deque_content γ frag2 -∗ False.
  Proof.
    iIntros "C1 C2".
      iDestruct "C1" as (γq γsw γdqst) "[%Enc C1]".
      iDestruct "C2" as (γq' γsw' γdqst') "[%Enc' C2]".
      encode_agree Enc.
    by iDestruct (own_valid_2 with "C1 C2") as %?%auth_frag_op_valid_1.
  Qed.

  (* TODO: move these to helpers.v *)
  Lemma own_ea_agree γ a b :
    own γ (●E a) -∗ own γ (◯E b) -∗ ⌜a = b⌝.
  Proof.
    iIntros "● ◯".
    by iDestruct (own_valid_2 with "● ◯") as %?%excl_auth_agree_L.
  Qed.

  Lemma own_ea_update a' γ a b :
    own γ (●E a) -∗ own γ (◯E b) ==∗ own γ (●E a') ∗ own γ (◯E a').
  Proof.
    iIntros "● ◯".
    iMod (own_update_2 γ _ _ (●E a' ⋅ ◯E a') with "● ◯") as "[● ◯]".
    - apply excl_auth_update.
    - by iFrame.
  Qed.

  Lemma new_deque_spec n :
    0 < n →
    {{{ True }}}
      new_deque #n
    {{{ γ q, RET q;
      is_deque γ q ∗ deque_content γ [] ∗ own_deque γ q
    }}}.
  Proof with extended_auto.
    iIntros (Hsz Φ) "_ HΦ". wp_lam.

    (* allocate *)
    wp_alloc arr as "[arr↦1 arr↦2]"... wp_pures.
    wp_alloc bot as "[b↦1 b↦2]". wp_alloc top as "t↦". wp_pures.

    (* make resources *)
    iMod (own_alloc (●E [] ⋅ ◯E [])) as (γq) "[γq● γq◯]". 1: apply excl_auth_valid.
    iMod (dqst_auth_alloc (replicate n #0)) as (γdqst) "Auth"...
    iMod (ghost_var_alloc ((replicate n #0), 1, false)) as (γsw) "[Era1 Era2]".
    iMod (inv_alloc N _ (deque_inv γq γsw γdqst arr top bot)
      with "[t↦ b↦1 arr↦1 γq● Auth Era1]") as "Inv"; fr...

    (* apply Φ *)
    iApply "HΦ". iModIntro. iSplitL "Inv"; first fr.
    iSplitL "γq◯"; fr. fr.
  Qed.

  Lemma push_spec γ q (v : val) :
    is_deque γ q -∗
    own_deque γ q -∗
    <<< ∀∀ l : list val, deque_content γ l >>>
      push q v @ ↑N
    <<< deque_content γ (l ++ [v]),
      RET #(), own_deque γ q >>>.
  Proof with extended_auto.
    iIntros "#Is Own" (Φ) "AU".
      iDestruct "Own" as (γq γsw) "Own".
        iDestruct "Own" as (γdqst l arr top bot b) "Own".
        iDestruct "Own" as "(%Enc & %Q & swOwn & AOwn & bOwn)".
        subst q.
      iDestruct "Is" as (γq' γsw' γdqst') "Inv".
        iDestruct "Inv" as (n' arr' top' bot') "Inv".
        iDestruct "Inv" as "(%Q & %Enc' & Inv)".
        injection Q as [= Hn <- <- <-]. encode_agree Enc.
    wp_lam. unfold sz, code.arr, code.top, code.bot. wp_pures.
    wp_load. wp_pures.

    (* 1. load top *)
    wp_bind (! _)%E.
      iInv "Inv" as (l1 t1 b1 pop1) ">Invs".
        iDestruct "Invs" as "(%Htb1 & ● & Sw & Dqst & A & T & B)".
      iDestruct (ghost_var_agree with "swOwn Sw") as "%Eq"; injection Eq as [= <- <- <-].
      iDestruct (dqst_get_frag with "Dqst") as "#F1".
      wp_load.
    iModIntro. iSplitL "● Sw Dqst A T B".
    { iExists l. fr. }
    wp_pures.

    case_bool_decide; wp_pures. { admit. }
    
    (* 2. write to circle *)
    rewrite rem_mod_eq...
    wp_bind (_ <- _)%E.
      iInv "Inv" as (l2 t2 b2 pop2) ">Invs".
        iDestruct "Invs" as "(%Htb2 & ● & Sw & Dqst & A & T & B)".
      iDestruct (ghost_var_agree with "swOwn Sw") as "%Eq"; injection Eq as [= <- <- <-].
      iMod (ghost_var_update_halves ((mod_set l b v), b, false) with "swOwn Sw") as "[swOwn Sw]".
      iDestruct (dqst_auth_write_bot v with "Dqst") as "Dqst".
      iCombine "AOwn A" as "A".
        iApply (wp_store_offset with "A"). 1: apply mod_get_is_Some...
      iIntros "!> [AOwn A]".
    iModIntro. iSplitL "● Sw Dqst A T B".
    { iExists (mod_set l b v),t2,b... rewrite circ_slice_update_right... fr. }
    wp_pures.

    (* 3. increment bot *)
    iInv "Inv" as (l3 t3 b3 pop3) ">Invs".
      iDestruct "Invs" as "(%Htb3 & ● & Sw & Dqst & A & T & B)".
      iDestruct (ghost_var_agree with "swOwn Sw") as "%Eq"; injection Eq as [= <- <- <-].
        rewrite mod_set_length in Htb3.
      iMod (ghost_var_update_halves ((mod_set l b v), S b, false) with "swOwn Sw") as "[swOwn Sw]".
      iDestruct (dqst_get_lb with "Dqst F1") as "%Ht13".
        iMod (dqst_auth_push with "Dqst") as "Dqst"...
      iCombine "bOwn B" as "B". wp_store.
        replace (Z.of_nat b + 1)%Z with (Z.of_nat (S b))...
      iDestruct "B" as "[bOwn B]".
    iMod "AU" as (l') "[Cont [_ Commit]]".
      iDestruct "Cont" as (γq' γsw' γbglob') "[%Enc' ◯]". encode_agree Enc.
      iDestruct (own_ea_agree with "● ◯") as "%Hl'".
      iMod (own_ea_update (l' ++ [v]) with "● ◯") as "[● ◯]".
      iMod ("Commit" with "[◯]") as "HΦ". 1: fr.
    iModIntro. iSplitL "● Sw Dqst A T B".
    { iExists (mod_set l b v), t3, (S b). fr.
      rewrite (circ_slice_extend_right _ _ _ v)... 2: rewrite mod_set_get...
      subst l'. fr. }
    iApply "HΦ".
      iExists γq, γsw, γdqst.
      iExists (mod_set l b v), arr, top, bot, (S b). fr.
  Admitted.

  Lemma pop_spec γ q :
    is_deque γ q -∗
    own_deque γ q -∗
    <<< ∀∀ l : list val, deque_content γ l >>>
      pop q @ ↑N
    <<< ∃∃ (l' : list val) (ov : val),
        deque_content γ l' ∗
        match ov with
        | NONEV => ⌜l = l'⌝
        | SOMEV v => ⌜l = l' ++ [v]⌝
        | _ => False
        end,
      RET ov, own_deque γ q >>>.
  Proof with extended_auto.
    iIntros "#Is Own" (Φ) "AU".
      iDestruct "Own" as (γq γsw) "Own".
        iDestruct "Own" as (γdqst l arr top bot b) "Own".
        iDestruct "Own" as "(%Enc & %Q & swOwn & AOwn & bOwn)".
        subst q.
      iDestruct "Is" as (γq' γsw' γdqst') "Inv".
        iDestruct "Inv" as (n' arr' top' bot') "Inv".
        iDestruct "Inv" as "(%Q & %Enc' & Inv)".
        injection Q as [= Hn <- <- <-]. encode_agree Enc.
    wp_lam. unfold sz, code.arr, code.top, code.bot. wp_pures.
    wp_load. wp_pures.

    (* 1. decrement bot *)
    wp_bind (_ <- _)%E.
      iInv "Inv" as (l1 t1 b1 pop1) ">Invs".
        iDestruct "Invs" as "(%Htb1 & ● & Sw & Dqst & A & T & B)".
      iDestruct (ghost_var_agree with "swOwn Sw") as "%Eq"; injection Eq as [= <- <- <-].
      iMod (ghost_var_update_halves (l, b, true) with "swOwn Sw") as "[swOwn Sw]".
      iCombine "bOwn B" as "B". wp_store.
      iDestruct "B" as "[bOwn B]".
    iModIntro. iSplitL "● Sw Dqst A T B".
    { iExists l. fr. }
    wp_pures.

    (* 2. load top *)
    wp_bind (! _)%E.
      iInv "Inv" as (l2 t2 b2 pop2) ">Invs".
        iDestruct "Invs" as "(%Htb2 & ● & Sw & Dqst & A & T & B)".
      iDestruct (ghost_var_agree with "swOwn Sw") as "%Eq"; injection Eq as [= <- <- <-].
      wp_load.

    destruct (decide (t2 < b-1)).
    { (* normal case, this point is the commit point *)
      iMod "AU" as (l') "[Cont [_ Commit]]".
        iDestruct "Cont" as (γq' γsw' γdqst') "[%Enc' ◯]". encode_agree Enc.
        destruct (mod_get_is_Some l (b-1)) as [x Hx]...
        iDestruct (own_ea_agree with "● ◯") as "%Eq". subst l'.
        iMod (own_ea_update (circ_slice l t2 (b-1)) with "● ◯") as "[● ◯]".
        iMod (ghost_var_update_halves (l, b-1, false) with "swOwn Sw") as "[swOwn Sw]".
        iMod (dqst_auth_pop with "Dqst") as "Dqst"...
      iMod ("Commit" $! (circ_slice l t2 (b-1)) (SOMEV x) with "[◯]") as "HΦ".
      { fr. rewrite -circ_slice_extend_right... replace (S (b-1)) with b... }
      iModIntro. iSplitL "● Sw Dqst A T B".
      { iExists l,t2. fr. fr. replace (Z.of_nat b - 1)%Z with (Z.of_nat (b - 1))%Z... }
      wp_pures.

      case_bool_decide... wp_pures.
      replace (Z.of_nat b - 1)%Z with (Z.of_nat (b - 1))%Z... rewrite rem_mod_eq...
      wp_bind (! _)%E. iApply (wp_load_offset with "AOwn")...
      iIntros "!> AOwn". wp_pures.
      case_bool_decide... wp_pures.
      iApply "HΦ". iExists _,_,_, l. fr.
    }

    iModIntro. iSplitL "● Sw Dqst A T B".
    { iExists l. fr. }
    wp_pures.

    case_bool_decide; wp_pures.
    { (* empty *)
      assert (t2 = b)... subst t2.
      (* 3. roll back bot *)
      wp_bind (_ <- _)%E.
        iInv "Inv" as (l3 t3 b3 pop3) ">Invs".
          iDestruct "Invs" as "(%Htb3 & ● & Sw & Dqst & A & T & B)".
        iDestruct (ghost_var_agree with "swOwn Sw") as "%Eq"; injection Eq as [= <- <- <-].
        iMod (ghost_var_update_halves (l, b, false) with "swOwn Sw") as "[swOwn Sw]".
        iCombine "bOwn B" as "B". wp_store.
        iDestruct "B" as "[bOwn B]".
        iMod "AU" as (l') "[Cont [_ Commit]]".
      iMod ("Commit" $! l' NONEV with "[Cont]") as "HΦ"...
      iModIntro. iSplitL "● Sw Dqst A T B".
      { iExists l. fr. }
      wp_pures. iApply "HΦ". iExists _,_,_, l. fr.
    }
    
    (* non-empty *)
    replace (Z.of_nat b - 1)%Z with (Z.of_nat (b - 1))%Z... rewrite rem_mod_eq...
    wp_bind (! _)%E.
    destruct (mod_get_is_Some l (b-1)) as [v Hv]...
    iApply (wp_load_offset with "AOwn")...
    iIntros "!> AOwn". wp_pures.
    
    (* we already did normal case *)
    case_bool_decide... wp_pures.
    
    (* 3. CAS for one-element case *)
    assert (b = S t2)... subst b.
    wp_bind (CmpXchg _ _ _)%E.
      iInv "Inv" as (l3 t3 b3 pop3) ">Invs".
        iDestruct "Invs" as "(%Htb3 & ● & Sw & Dqst & A & T & B)".
      iDestruct (ghost_var_agree with "swOwn Sw") as "%Eq"; injection Eq as [= <- <- <-].
    destruct (decide (t2 = t3)).


















































    + (* success *)
      subst t3. wp_cmpxchg_suc.
        replace (Z.of_nat t2 + 1)%Z with (Z.of_nat (S t2))...
      iMod "AU" as (l') "[Cont [_ Commit]]".
        iDestruct "Cont" as (γq' γsw' γdqst') "[%Enc' ◯]". encode_agree Enc.
        destruct (mod_get_is_Some l (S t2 - 1)) as [x Hx]...
          rewrite Hv in Hx. injection Hx as [= <-].
        iMod (dqst_auth_update with "Dqst") as "Dqst"...
        iDestruct (own_ea_agree with "● ◯") as "%Eq". subst l'.
        iMod (own_ea_update [] with "● ◯") as "[● ◯]".
      iMod ("Commit" $! [] (SOMEV v) with "[◯]") as "HΦ".
      { fr. rewrite (circ_slice_extend_right _ _ _ v)...
        1: rewrite circ_slice_nil... replace t2 with (S t2 - 1)... }
      iModIntro. iSplitL "● Sw Dqst A T B".
      { iExists γera, arr, l, (S t2), (S t2).
        rewrite circ_slice_nil... fr. fr. }
      wp_pures.

      (* 4. roll back bot *)
      wp_bind (_ <- _)%E.
        iInv "Inv" as (γera4 ca4 l4 t4 b4 pop4) ">Invs".
          iDestruct "Invs" as "(%Htb4 & ● & Sw & Dqst & A & T & B)".
        iDestruct (ghost_var_agree with "swOwn Sw") as "%Eq"; injection Eq as [= <- <- <-].
        replace (Z.of_nat (S t2 - 1))%Z with (Z.of_nat t2)%Z...
        replace (Z.of_nat (S t2) - 1)%Z with (Z.of_nat t2)%Z...
        iMod (ghost_var_update_halves (γera, arr, l, S t2, false)
          with "swOwn Sw") as "[swOwn Sw]".
        iCombine "bOwn B" as "B". wp_store.
          replace (Z.of_nat t2 + 1)%Z with (Z.of_nat (S t2))%Z...
        iDestruct "B" as "[bOwn B]".
      iModIntro. iSplitL "● Sw Dqst A T B".
      { iExists _,_,l. fr. }
      wp_pures. iApply "HΦ". iExists _,_,_, _,l. fr.
    + (* fail *)
      wp_cmpxchg_fail. { intro NO. injection NO... }
      iMod "AU" as (l') "[Cont [_ Commit]]".
      iMod ("Commit" $! l' NONEV with "[Cont]") as "HΦ"...
      iModIntro. iSplitL "● Sw Dqst A T B".
      { iExists _,_,l. fr. }
      wp_pures.

      (* 4. roll back bot *)
      wp_bind (_ <- _)%E.
        iInv "Inv" as (γera4 ca4 l4 t4 b4 pop4) ">Invs".
          iDestruct "Invs" as "(%Htb4 & ● & Sw & Dqst & A & T & B)".
        iDestruct (ghost_var_agree with "swOwn Sw") as "%Eq"; injection Eq as [= <- <- <-].
        replace (Z.of_nat (S t2 - 1))%Z with (Z.of_nat t2)%Z...
        replace (Z.of_nat (S t2) - 1)%Z with (Z.of_nat t2)%Z...
        iMod (ghost_var_update_halves (γera, arr, l, S t2, false)
          with "swOwn Sw") as "[swOwn Sw]".
        iCombine "bOwn B" as "B". wp_store.
          replace (Z.of_nat t2 + 1)%Z with (Z.of_nat (S t2))%Z...
        iDestruct "B" as "[bOwn B]".
      iModIntro. iSplitL "● Sw Dqst A T B".
      { iExists _,_,l. fr. }
      wp_pures. iApply "HΦ". iExists _,_,_, _,l. fr.
  Qed.

  Lemma steal_spec γ q :
    is_deque γ q -∗
    <<< ∀∀ l : list val, deque_content γ l >>>
      steal q @ ↑N
    <<< ∃∃ (l' : list val) (ov : val),
        deque_content γ l' ∗
        match ov with
        | NONEV => ⌜l = l'⌝
        | SOMEV v => ⌜l = [v] ++ l'⌝
        | _ => False
        end,
      RET ov >>>.
  Proof with extended_auto.
    iIntros "#Is" (Φ) "AU".
    iDestruct "Is" as (γq γsw γdqst) "Inv".
      iDestruct "Inv" as (arr top bot) "Inv".
      iDestruct "Inv" as "(%Q & %Enc & Inv)".
      subst q.
    wp_lam. unfold code.arr, code.top, code.bot, circ_access. wp_pures.

    (* 1. load top *)
    wp_bind (! _)%E.
      iInv "Inv" as (γera1 ca1 l1 t1 b1 pop1) ">Invs".
        iDestruct "Invs" as "(%Htb1 & ● & Sw & Dqst & A & T & B)".
      iDestruct (dqst_get_frag with "Dqst") as "#F1".
      wp_load.
    iModIntro. iSplitL "● Sw Dqst A T B".
    { iExists _,_,l1. fr. }
    wp_pures.

    (* 2. load bot *)
    wp_bind (! _)%E.
      iInv "Inv" as (γera2 ca2 l2 t2 b2 pop2) ">Invs".
        iDestruct "Invs" as "(%Htb2 & ● & Sw & Dqst & A & T & B)".
      iDestruct (dqst_get_frag with "Dqst") as "#F2".
      iDestruct (dqst_get_lb with "Dqst F1") as "%Lb12".
      wp_load.
    iModIntro. iSplitL "● Sw Dqst A T B".
    { iExists _,_,l2. fr. }
    wp_pures.

    (* 3. load array *)
    wp_bind (! _)%E.
      iInv "Inv" as (γera3 ca3 l3 t3 b3 pop3) ">Invs".
        iDestruct "Invs" as "(%Htb3 & ● & Sw & Dqst & A & T & B)".
      iDestruct (dqst_get_frag with "Dqst") as "#F3".
      iDestruct (dqst_get_lb with "Dqst F2") as "%Lb23".
      wp_load.
    iModIntro. iSplitL "● Sw Dqst A T B".
    { iExists _,_,l3. fr. }
    wp_pures.

    (* no chance to steal *)
    replace (if pop2 then LitInt (Z.of_nat b2 - 1) else LitInt (Z.of_nat b2))
      with (LitInt (Z.of_nat (if pop2 then (b2 - 1) else b2))).
      2: { destruct pop2... replace (Z.of_nat b2 - 1)%Z with (Z.of_nat (b2 - 1))... }
    wp_pures.
    case_bool_decide as Hif; wp_pures.
    { iMod "AU" as (l) "[Cont [_ Commit]]".
      iMod ("Commit" $! l NONEV with "[Cont]") as "Φ"...
      iApply "Φ"... }
    assert (t1 < b2) as Htb12. 1: destruct pop2...

    (* 4. get_circle *)
    rewrite rem_mod_eq...
    wp_bind (! _)%E.
      iInv "Inv" as (γera4 ca4 l4 t4 b4 pop4) ">Invs".
        iDestruct "Invs" as "(%Htb4 & ● & Sw & Dqst & A & T & B)".
      iDestruct (dqst_get_frag with "Dqst") as "#F4".
      iDestruct (dqst_get_lb with "Dqst F3") as "%Lb34".
    destruct (decide (γera3 = γera4)) as [eqγ|neqγ].
    - (* array was not archived *)
      subst γera4.
        iDestruct (dqst_frag_agree with "F3 F4") as "[%H34 %Hlen]".
          subst ca4. rewrite Hlen. clear Hlen.
        destruct (mod_get_is_Some l4 t1) as [v Hv]...
        iApply (wp_load_offset with "A")...
        iIntros "!> A".
      iModIntro. iSplitL "● Sw Dqst A T B".
      { iExists _,_,l4. fr. }
      wp_pures.
      
      (* 5. CAS *)
      wp_bind (CmpXchg _ _ _)%E.
      iInv "Inv" as (γera5 ca5 l5 t5 b5 pop5) ">Invs".
        iDestruct "Invs" as "(%Htb5 & ● & Sw & Dqst & A & T & B)".
        iDestruct (dqst_get_frag with "Dqst") as "#F5".
        iDestruct (dqst_get_lb with "Dqst F4") as "%Lb45".
      destruct (decide (t1 = t5)); last first.
      { (* fail *)
        wp_cmpxchg_fail. { intro NO. inversion NO... }
        iMod "AU" as (lau) "[Cont [_ Commit]]".
        iMod ("Commit" $! lau NONEV with "[Cont]") as "HΦ"...
        iModIntro. iSplitL "● Sw Dqst A T B".
        { iExists _,_,l5. fr. }
        wp_pures. iApply "HΦ"...
      }
      (* success *)
      subst t5. wp_cmpxchg_suc.
        replace (Z.of_nat t1 + 1)%Z with (Z.of_nat (S t1))...
        assert (t1 = t2)... subst t2.
        assert (t1 = t3)... subst t3. assert (t1 < b3) as Htb13...
        assert (t1 = t4)... subst t4. assert (t1 < b4) as Htb14...
        assert (t1 < b5) as Htb15...
        assert (mod_get l5 t1 = Some v) as Hv5.
        { replace (mod_get l5 t1) with (mod_get l4 t1)...
          apply Lb45... }
      iMod "AU" as (lau) "[Cont [_ Commit]]".
        iDestruct "Cont" as (γq' γsw' γdqst') "[%Enc' ◯]". encode_agree Enc'.
        iDestruct (own_ea_agree with "● ◯") as "%Hlau". subst lau.
        rewrite (circ_slice_shrink_left _ _ _ v)...
        iMod (own_ea_update (circ_slice l5 (S t1) b5)
          with "● ◯") as "[● ◯]".
        iMod (dqst_auth_update with "Dqst") as "Dqst"...
      iMod ("Commit" $! (circ_slice l5 (S t1) b5) (SOMEV v)
        with "[◯]") as "HΦ"; fr.
      iModIntro. iSplitL "● Sw Dqst A T B".
      { iExists _,_,l5. fr. fr. }
      wp_pures. iApply "HΦ"...
    - (* array was archived *)
      iDestruct (dqst_get_archived with "Dqst F3") as (l' t' b') "[Arch [Arr Close]]"...
        iDestruct (dqst_archived_get_lb with "Arch F3") as "%Ht3'".
        iDestruct (dqst_archived_get_frag with "Arch") as "#F'".
        iDestruct (dqst_frag_agree with "F3 F'") as "[_ %Hl3']".
        rewrite Hl3'. destruct (mod_get_is_Some l' t1) as [v Hv]...
        iApply (wp_load_offset with "Arr")... iIntros "!> Arr".
      iDestruct ("Close" with "Arch Arr") as "Dqst".
      iDestruct (dqst_get_lb with "Dqst F'") as "%Lb'4".
      iSplitL "● Sw Dqst A T B".
      { iExists _,_,l4. fr. }
      iModIntro. wp_pures.

      (* 5. CAS *)
      wp_bind (CmpXchg _ _ _)%E.
      iInv "Inv" as (γera5 ca5 l5 t5 b5 pop5) ">Invs".
        iDestruct "Invs" as "(%Htb5 & ● & Sw & Dqst & A & T & B)".
        iDestruct (dqst_get_frag with "Dqst") as "#F5".
        iDestruct (dqst_get_lb with "Dqst F4") as "%Lb45".
      destruct (decide (t1 = t5)); last first.
      { (* fail *)
        wp_cmpxchg_fail. { intro NO. inversion NO... }
        iMod "AU" as (lau) "[Cont [_ Commit]]".
        iMod ("Commit" $! lau NONEV with "[Cont]") as "HΦ"...
        iModIntro. iSplitL "● Sw Dqst A T B".
        { iExists _,_,l5. fr. }
        wp_pures. iApply "HΦ"...
      }
      (* success *)
      subst t5. wp_cmpxchg_suc.
        replace (Z.of_nat t1 + 1)%Z with (Z.of_nat (S t1))...
        assert (t1 = t2)... subst t2.
        assert (t1 = t3)... subst t3. assert (t1 < b3) as Htb13...
        assert (t1 = t4)... subst t4. assert (t1 < b4) as Htb14...
        assert (t1 = t')... subst t'. assert (t1 < b') as Htb1'...
        assert (t1 < b5) as Htb15...
        assert (mod_get l5 t1 = Some v) as Hv5.
        { replace (mod_get l5 t1) with (mod_get l4 t1)...
          - rewrite -Hv. symmetry. apply Lb'4...
          - apply Lb45... }
      iMod "AU" as (lau) "[Cont [_ Commit]]".
        iDestruct "Cont" as (γq' γsw' γdqst') "[%Enc' ◯]". encode_agree Enc'.
        iDestruct (own_ea_agree with "● ◯") as "%Hlau". subst lau.
        rewrite (circ_slice_shrink_left _ _ _ v)...
        iMod (own_ea_update (circ_slice l5 (S t1) b5)
          with "● ◯") as "[● ◯]".
        iMod (dqst_auth_update with "Dqst") as "Dqst"...
      iMod ("Commit" $! (circ_slice l5 (S t1) b5) (SOMEV v)
        with "[◯]") as "HΦ"; fr.
      iModIntro. iSplitL "● Sw Dqst A T B".
      { iExists _,_,l5. fr. fr. }
      wp_pures. iApply "HΦ"...
  Qed.
End proof.

Program Definition atomic_deque `{!heapGS Σ, !dequeG Σ, !circleG Σ} :
  spec.atomic_deque Σ :=
  {| spec.new_deque_spec := new_deque_spec;
     spec.push_spec := push_spec;
     spec.pop_spec := pop_spec;
     spec.steal_spec := steal_spec;
     spec.deque_content_exclusive := deque_content_exclusive |}.

Global Typeclasses Opaque deque_content is_deque.
