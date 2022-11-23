From iris.algebra Require Import excl auth list.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import invariants ghost_var mono_nat.
From chase_lev Require Import atomic.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import proofmode notation.
From iris.prelude Require Import options.
From chase_lev Require Import mono_list.
From chase_lev.circular Require Import helpers spec.

Definition CAP_CONST : nat := 20.

(*
We use a finite length circular list without resizing.
The push function diverges on overflow.

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
  since t starts from 1 (because we need to reason about
  t-1). As such, it can be any value.

Invariants:
- top |-> t
- bot |-> b if "not popping", otherwise bot |-> b-1
- arr |-> l
- those in history are preserved (done by mono_list)
- top always increases (done by mono_nat)
- l and history matches at top
*)

Section code.
  (* t and b start from 1 because we have to be able to decrement b *)
  Definition new_deque : val :=
    λ: <>,
      let: "array" := AllocN #CAP_CONST #0 in
      ("array", ref #1, ref #1). (* array, top, bottom *)
  
  Definition arr : val := λ: "deque", Fst (Fst "deque").
  Definition top : val := λ: "deque", Snd (Fst "deque").
  Definition bot : val := λ: "deque", Snd "deque".
  Definition loop : val := (rec: "loop" "x" := "loop" "x").

  Definition push : val :=
    λ: "deque" "v",
      let: "array" := arr "deque" in
      let: "b" := !(bot "deque") in
      if: !(top "deque") + #CAP_CONST ≤ "b" then loop #() else
      "array" +ₗ ("b" `rem` #CAP_CONST) <- "v" ;;
      bot "deque" <- "b" + #1.
  
  Definition pop : val :=
    λ: "deque",
      let: "array" := arr "deque" in
      let: "b" := !(bot "deque") - #1 in
      bot "deque" <- "b" ;;
      let: "t" := !(top "deque") in
      if: "b" < "t" then (* empty pop *)
        bot "deque" <- "t" ;; NONE
      else let: "v" := !("array" +ₗ ("b" `rem` #CAP_CONST)) in
      if: "t" < "b" then SOME "v" (* normal case *)
      else let: "ok" := CAS (top "deque") "t" ("t" + #1) in
      bot "deque" <- "t" + #1 ;;
      if: "ok" then SOME "v" (* popped *)
      else NONE. (* stolen *)

  (* NOTE: b ≤ t doesn't necessarily mean the deque was empty!
    It can also be the case that there was one element and
    the owner thread prematurely decremented b trying to pop. *)
  Definition steal : val :=
    λ: "deque",
      let: "array" := arr "deque" in
      let: "t" := !(top "deque") in
      let: "b" := !(bot "deque") in
      if: "b" ≤ "t" then NONE (* no chance *)
      else let: "v" := !("array" +ₗ ("t" `rem` #CAP_CONST)) in
      if: CAS (top "deque") "t" ("t" + #1)
      then SOME "v" (* success *)
      else NONE. (* fail *)
End code.

(** The CMRA we need. *)

Class dequeG Σ := DequeG {
    deque_tokG :> ghost_varG Σ (list val);
    deque_popG :> ghost_varG Σ bool;
    mono_listG :> mono_listG val Σ;
    mono_natG :> mono_natG Σ
  }.
Definition dequeΣ : gFunctors :=
  #[ghost_varΣ (list val);
    ghost_varΣ bool;
    mono_listΣ val;
    mono_natΣ
  ].
Global Instance subG_dequeΣ {Σ} : subG dequeΣ Σ → dequeG Σ.
Proof. solve_inG. Qed.

Section RA.
  Context `{!heapGS Σ, !dequeG Σ} (N : namespace).
  Notation iProp := (iProp Σ).

  Definition mono_deque_auth_own (γm : gname) (hl : list val) (t b : nat) : iProp :=
    ∃ (γl γt : gname),
    ⌜γm = encode (γl, γt)⌝ ∗
    ⌜(length hl = t ∧ t = b) ∨ (length hl = S t ∧ t < b)⌝ ∗
    mono_list_auth_own γl 1 hl ∗
    mono_nat_auth_own γt 1 t.

  Definition mono_deque_lb_own (γm : gname) (hl : list val) (t b : nat) : iProp :=
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
    iMod (mono_deque_steal _ #() with "D"). 1: lia.
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
    destruct HU as [[Ht [v Hl]]|[Ht Hl]];
    destruct BOUND as [[Hl1 Hb]|[Hl1 Hb]]; try lia; subst.
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
    destruct BOUND as [[Hl1 Hb]|[Hl1 Hb]]; try lia.
    iExists _,_. repeat iSplit; auto; iFrame.
  Qed.
End RA.

Section proof.
  Context `{!heapGS Σ, !dequeG Σ} (N : namespace).
  Notation iProp := (iProp Σ).

  Definition deque_inv (γ : gname) (arr top bot : loc) : iProp :=
    ∃ (γq γpop γm : gname) (t b : nat) (l : list val) (Popping : bool),
      ⌜γ = encode (γq, γpop, γm)⌝ ∗
      ⌜1 ≤ t ≤ b ∧ length l = CAP_CONST⌝ ∗
      (* physical data *)
      ( let bp := if Popping then b-1 else b in
        top ↦ #t ∗ bot ↦{#1/2} #bp ∗ arr ↦∗{#1/2} l
      ) ∗
      (* logical data *)
      ( ghost_var γq (1/2) (circ_slice l t b) ∗
        ghost_var γpop (1/2) Popping
      ) ∗
      (* history of determined elements *)
      ( ∃ (hl : list val),
        mono_deque_auth_own γm hl t b ∗
        ⌜t < b → hl !! t = mod_get l t⌝
      ).

  Definition is_deque (γ : gname) (q : val) : iProp :=
    ∃ (arr top bot : loc),
      ⌜q = (#arr, #top, #bot)%V⌝ ∗
      inv N (deque_inv γ arr top bot).
  Global Instance is_deque_persistent γ q :
    Persistent (is_deque γ q) := _.

  Definition deque_content (γ : gname) (frag : list val) : iProp :=
    ∃ (γq γpop γm : gname),
      ⌜γ = encode (γq, γpop, γm)⌝ ∗
      ghost_var γq (1/2) frag.

  Definition own_deque (γ : gname) (q : val) : iProp :=
    ∃ (γq γpop γm : gname) (arr top bot : loc) (b : nat) (l : list val),
      ⌜γ = encode (γq, γpop, γm)⌝ ∗
      ⌜q = (#arr, #top, #bot)%V⌝ ∗
      ⌜length l = CAP_CONST⌝ ∗
      ghost_var γpop (1/2) false ∗
      bot ↦{#1/2} #b ∗ arr ↦∗{#1/2} l.
  
  Lemma loop_spec v :
    {{{ True }}} loop #v {{{ RET #(); False }}}.
  Proof.
    iIntros (Φ) "_ HΦ". wp_rec. iLöb as "IH". wp_rec.
    by iApply "IH".
  Qed.

  Ltac extended_auto :=
    eauto; unfold CAP_CONST in *; unfold helpers.CAP_CONST in *;
    try by (
      repeat iNext; repeat iIntros; repeat intros;
      try case_decide; try iPureIntro;
      try rewrite lookup_lt_is_Some;
      try rewrite Qp.half_half;
      try lia; done
    ).
  Ltac fr :=
    repeat iSplit; extended_auto; repeat iExists _;
    try iFrame "arr↦"; try iFrame "arr↦1"; try iFrame "arr↦2"; 
    iFrame; eauto.

  Lemma new_deque_spec :
    {{{ True }}}
      new_deque #()
    {{{ γ q, RET q;
      is_deque γ q ∗ deque_content γ [] ∗ own_deque γ q
    }}}.
  Proof with extended_auto.
    iIntros (Φ) "_ HΦ".
    wp_lam. wp_alloc arr as "[arr↦1 arr↦2]"...
    wp_pures. wp_alloc b as "[b↦1 b↦2]". wp_alloc t as "t↦".
    iMod (ghost_var_alloc []) as (γq) "[γq1 γq2]".
    iMod (ghost_var_alloc false) as (γpop) "[γpop1 γpop2]".
    iMod (mono_deque_own_alloc #0) as (γm) "γm".
    iMod (inv_alloc N _ (deque_inv (encode (γq, γpop, γm)) arr t b)
      with "[t↦ b↦1 arr↦1 γq1 γpop1 γm]") as "Inv".
    { iExists _,_,_, 1,1,(replicate 20 #0),false. fr. fr... }
    wp_pures. iModIntro. iApply "HΦ". fr.
    iSplitL "γq2". 1: fr. iExists _,_,_, _,_,_,1,_. fr.
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
      iDestruct "Own" as (γq γpop γm arr top bot b l)
        "(%Enc & -> & %HL & γ👑 & b👑 & arr👑)".
      iDestruct "Is" as (arr' top' bot') "[%Is Inv]".
      injection Is as [= <- <- <-].
    wp_lam. unfold code.arr, code.top, code.bot. wp_pures.

    (* load bot *)
    wp_load. wp_pures.

    (* load top *)
    wp_bind (! _)%E.
      iInv "Inv" as (γq' γpop' γm' t0 b0 l0 Pop0)
        ">(%Enc' & %Bound0 & Phys & Abst & Mono)".
        encode_agree Enc.
      iDestruct "Abst" as "[Q P]".
        iDestruct (ghost_var_agree with "γ👑 P") as "%". subst Pop0.
      iCombine "Q P" as "Abst".
      iDestruct "Phys" as "(t↦ & b↦ & arr↦)". wp_load.
        iDestruct (mapsto_agree with "b↦ b👑") as "%".
          injection H as [=]. apply Nat2Z.inj in H. subst b0.
        iDestruct (array_agree with "arr↦ arr👑") as "%"... subst l0.
      iCombine "t↦ b↦ arr↦" as "Phys".
      iDestruct "Mono" as (hl) "[Mono %HistPref0]".
        iDestruct (mono_deque_get_lb with "Mono") as "#Mlb0".
    iModIntro. iSplitL "Phys Abst Mono".
      { iExists _,_,_, t0,b,l,false. fr... }
    wp_pures.

    (* diverge *)
    case_bool_decide as HbC. { wp_pures. iApply loop_spec... }
    wp_pures. rewrite rem_mod_eq...

    (* store value *)
    wp_bind (_ <- _)%E.
      iInv "Inv" as (γq' γpop' γm' t1 b1 l1 Pop1)
        ">(%Enc' & %Bound1 & Phys & Abst & Mono)".
        encode_agree Enc.
      iDestruct "Abst" as "[Q P]".
        iDestruct (ghost_var_agree with "γ👑 P") as "%". subst Pop1.
      iCombine "Q P" as "Abst".
      iDestruct "Phys" as "(t↦ & b↦ & arr↦)".
        iDestruct (mapsto_agree with "b↦ b👑") as "%".
          injection H as [=]. apply Nat2Z.inj in H. subst b1.
        iDestruct (array_agree with "arr↦ arr👑") as "%"... subst l1.
        iCombine "arr↦ arr👑" as "arr↦".
        iApply (wp_store_offset with "arr↦").
        { rewrite <- HL. apply mod_get_is_Some... }
        replace (<[b `mod` 20:=v]> l) with (mod_set l b v).
          2: rewrite -HL...
        iNext. iIntros "[arr↦ arr👑]".
      iCombine "t↦ b↦ arr↦" as "Phys".
      iDestruct "Mono" as (hl1) "[Mono %HistPref1]".
        iDestruct (mono_deque_auth_history with "Mono") as "%Hist1".
      iDestruct (mono_deque_auth_lb_top with "Mono Mlb0") as "%Ht01".
      iModIntro. iSplitL "Phys Abst Mono".
      { iExists _,_,_, t1,b,(mod_set l b v),false.
        rewrite insert_length. fr...
        rewrite circ_slice_update_right...
        fr. fr. iIntros "%". rewrite mod_set_get_ne...
        apply neq_symm, mod_neq... }
    wp_pures.
    replace (Z.of_nat b + 1)%Z with (Z.of_nat (S b))...

    (* store bot *)
    iInv "Inv" as (γq' γpop' γm' t2 b2 l2 Pop2)
        ">(%Enc' & %Bound2 & Phys & Abst & Mono)".
        encode_agree Enc.
      iMod "AU" as (q) "[Cont [_ Commit]]".
        iDestruct "Cont" as (γq' γpop' γm') "[%Enc' Cont]".
        encode_agree Enc.
      iDestruct "Abst" as "[Q P]".
        iDestruct (ghost_var_agree with "Q Cont") as "%". subst q.
        iMod (ghost_var_update_2 (circ_slice l2 t2 (S b))
          with "Q Cont") as "[Q Cont]"...
        iDestruct (ghost_var_agree with "γ👑 P") as "%". subst Pop2.
      iCombine "Q P" as "Abst".
      iDestruct "Phys" as "(t↦ & b↦ & arr↦)".
        iDestruct (mapsto_agree with "b↦ b👑") as "%".
          injection H as [=H]. apply Nat2Z.inj in H. subst b2.
        iDestruct (array_agree with "arr↦ arr👑") as "%"...
          1: rewrite insert_length... subst l2.
        iCombine "b↦ b👑" as "b↦". wp_store.
        iDestruct "b↦" as "[b↦ b👑]".
      iCombine "t↦ b↦ arr↦" as "Phys".
      iDestruct "Mono" as (hl2) "[Mono %HistPref2]".
        iDestruct (mono_deque_auth_history with "Mono") as "%Hist2".
        iMod (mono_deque_push _
          (if decide (t2 = b) then hl2 ++ [v] else hl2)
          (S b) with "Mono") as "Mono"...
        { destruct (decide (t2 = b))... right. split... }
      rewrite <- circ_slice_extend_right...
        2: rewrite mod_set_get...
      iMod ("Commit" with "[Cont]") as "Φ". 1: fr.
    iModIntro. iModIntro.

    iSplitL "Phys Abst Mono".
    { iExists _,_,_, t2,(S b),(mod_set l b v),false. fr... fr.
      case_decide.
      - subst. destruct Hist2 as [[Hist2 _]|NO]...
        rewrite lookup_app_r... rewrite mod_set_get...
        rewrite Hist2. replace (b-b) with 0...
      - iPureIntro; intros. apply HistPref2... }
    iApply "Φ". fr. fr.
  Qed.

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
      iDestruct "Own" as (γq γpop γm arr top bot b l)
        "(%Hγ & -> & %HL & γ👑 & b👑 & arr👑)".
      iDestruct "Is" as (arr' top' bot') "[%Is Inv]".
      injection Is as [= <- <- <-].
    wp_lam. unfold code.arr, code.top, code.bot. wp_pures.

    (* load bot *)
    wp_load. wp_pures.

    (* decrement b early *)
    wp_bind (_ <- _)%E.
      iInv "Inv" as (γq' γpop' γm' t1 b1 l1 Pop1)
        ">(%Enc & %Bound1 & Phys & Abst & Mono)".
        encode_agree Enc.
      iDestruct "Abst" as "[Q P]".
        iDestruct (ghost_var_agree with "γ👑 P") as "%". subst Pop1.
        iMod (ghost_var_update_2 true with "γ👑 P") as "[γ👑 P]"...
      iCombine "Q P" as "Abst".
      iDestruct "Phys" as "(t↦ & b↦ & arr↦)".
        iDestruct (mapsto_agree with "b↦ b👑") as "%".
          injection H as [=]. apply Nat2Z.inj in H. subst b1.
        iCombine "b↦ b👑" as "b↦". wp_store.
          replace (Z.of_nat b-1)%Z with (Z.of_nat (b-1))...
        iDestruct "b↦" as "[b↦ b👑]".
        iDestruct (array_agree with "arr↦ arr👑") as "%"... subst l1.
      iCombine "t↦ b↦ arr↦" as "Phys".
      iModIntro. iSplitL "Phys Abst Mono".
      { iExists _,_,_, t1,b,_,_... fr. }
    wp_pures.

    (* load top *)
    wp_bind (! _)%E.
      iInv "Inv" as (γq' γpop' γm' t2 b2 l2 Pop2)
        ">(%Enc & %Bound2 & Phys & Abst & Mono)".
        encode_agree Enc.
      iDestruct "Abst" as "[Q P]".
        iDestruct (ghost_var_agree with "γ👑 P") as "%". subst Pop2.
      iCombine "Q P" as "Abst".
      iDestruct "Phys" as "(t↦ & b↦ & arr↦)".
        iDestruct (mapsto_agree with "b↦ b👑") as "%".
          injection H as [=]. apply Nat2Z.inj in H.
          assert (b = b2) by lia. subst b2. clear H.
        iDestruct (array_agree with "arr↦ arr👑") as "%"... subst l2.
      iCombine "t↦ b↦ arr↦" as "Phys".
    
    (* if t < b-1, this load is the commit point *)
    destruct (decide (t2 < b-1)).
    { iMod "AU" as (l') "[Cont [_ Commit]]".
        iDestruct "Cont" as (γq' γpop' γm') "[%Enc Cont]".
        encode_agree Enc.
      destruct (mod_get_is_Some l (b-1)) as [v Hv]...
      erewrite circ_slice_shrink_right...
      iDestruct "Phys" as "(t↦ & b↦ & arr↦)". wp_load.
      iCombine "t↦ b↦ arr↦" as "Phys".
      iDestruct "Abst" as "[Q P]".
        iDestruct (ghost_var_agree with "Cont Q") as "%". subst l'.
        iMod (ghost_var_update_2 (circ_slice l t2 (b-1)) with "Cont Q")
          as "[Cont Q]"...
        iMod (ghost_var_update_2 false with "γ👑 P") as "[γ👑 P]"...
      iCombine "Q P" as "Abst".
      iDestruct "Mono" as (hl1) "[Mono %HistPref1]".
        iDestruct (mono_deque_pop _ (b-1) with "Mono") as "Mono"...
      iMod ("Commit" $! (circ_slice l t2 (b-1)) (SOMEV v)
        with "[Cont]") as "Φ". 1: fr.
      iModIntro. iModIntro.
      
      iSplitL "Phys Abst Mono".
      { iExists _,_,_, t2,(b-1),l,false. fr. fr.
        iPureIntro; intros. apply HistPref1... }
      wp_pures. case_bool_decide... wp_pures.

      (* read [b2-1] *)
      wp_bind (! _)%E. rewrite rem_mod_eq...
      iApply (wp_load_offset with "arr👑"). 1: rewrite -HL...
      iNext. iIntros "arr👑".
      wp_pures. case_bool_decide... wp_pures. iApply "Φ". fr. }

    (* otherwise... *)
    iDestruct "Phys" as "(t↦ & b↦ & arr↦)". wp_load.
    iCombine "t↦ b↦ arr↦" as "Phys".
    iModIntro. iSplitL "Phys Abst Mono".
    { iExists _,_,_, t2,b,_,true... fr. }
    wp_pures.

    (* empty *)
    case_bool_decide as Hbt; wp_pures.
    { wp_bind (_ <- _)%E.
      iInv "Inv" as (γq' γpop' γm' t3 b3 l3 Pop3)
        ">(%Enc & %Bound3 & Phys & Abst & Mono)".
        encode_agree Enc.
      iDestruct "Abst" as "[Q P]".
        iDestruct (ghost_var_agree with "γ👑 P") as "%". subst Pop3.
        iMod (ghost_var_update_2 false with "γ👑 P") as "[γ👑 P]"...
      iCombine "Q P" as "Abst".
      iDestruct "Phys" as "(t↦ & b↦ & arr↦)".
        iDestruct (mapsto_agree with "b↦ b👑") as "%".
        injection H as [=]. assert (b = b3)... subst b3. clear H.
        replace t2 with b...
        iCombine "b👑 b↦" as "b↦". wp_store.
        iDestruct "b↦" as "[b👑 b↦]".
        iDestruct (array_agree with "arr↦ arr👑") as "%"... subst l3.
      iCombine "t↦ b↦ arr↦" as "Phys".
      (* AU *)
      iMod "AU" as (l') "[Cont [_ Commit]]".
      iMod ("Commit" $! l' NONEV with "[Cont]") as "Φ"...
      iModIntro. iSplitL "Phys Abst Mono".
      { iExists _,_,_, t3,b,_,false. fr. }
      wp_pures. iApply "Φ". fr.
    }
    
    (* read [b2-1] *)
    wp_bind (! _)%E. rewrite rem_mod_eq...
    destruct (mod_get_is_Some l (b-1)) as [v Hv]...
    iApply (wp_load_offset with "arr👑"). 1: rewrite -HL...
    iNext. iIntros "arr👑".
    wp_pures.

    (* cas top, we already handled normal pop *)
    case_bool_decide... clear H. wp_pures.
    wp_bind (CmpXchg _ _ _)%E.
      iInv "Inv" as (γq' γpop' γm' t3 b3 l3 Pop3)
        ">(%Enc & %Bound3 & Phys & Abst & Mono)".
        encode_agree Enc.
      iDestruct "Abst" as "[Q P]".
        iDestruct (ghost_var_agree with "γ👑 P") as "%". subst Pop3.
      iCombine "Q P" as "Abst".
      iDestruct "Phys" as "(t↦ & b↦ & arr↦)".
        iDestruct (mapsto_agree with "b↦ b👑") as "%".
          injection H as [=]. assert (b = b3)... subst b3. clear H.
        iDestruct (array_agree with "arr↦ arr👑") as "%"... subst l3.
      iCombine "t↦ b↦ arr↦" as "Phys".
    assert (t2 = b-1)... subst t2. clear n Hbt.
    replace (Z.of_nat (b-1) + 1)%Z with (Z.of_nat b)...
    destruct (decide (b-1 = t3)).
    - (* success *)
      subst t3.
      iDestruct "Phys" as "(t↦ & b↦ & arr↦)".
        wp_cmpxchg_suc.
      iCombine "t↦ b↦ arr↦" as "Phys".

      (* AU *)
      iMod "AU" as (l') "[Cont [_ Commit]]".
        iDestruct "Cont" as (γq' γpop' γm') "[%Enc Cont]".
        encode_agree Enc.
      iDestruct "Abst" as "[Q P]".
        iDestruct (ghost_var_agree with "Cont Q") as "%". subst l'.
        erewrite circ_slice_shrink_left... rewrite circ_slice_to_nil...
        iMod (ghost_var_update_2 [] with "Cont Q") as "[Cont Q]"...
      iCombine "Q P" as "Abst".
      iMod ("Commit" $! [] (SOMEV v) with "[Cont]") as "Φ". 1: fr.
      iDestruct "Mono" as (hl1) "[Mono %HistPref1]".
        iMod (mono_deque_pop_singleton _ _ (b-1) with "[Mono]") as "Mono".
        { replace (S (b-1)) with b... }
      replace (S (b-1)) with b...
      iModIntro. iSplitL "Phys Abst Mono".
        { iExists _,_,_, b,b,_,true. fr.
          rewrite circ_slice_to_nil... fr. fr... }
      wp_pures.

      (* store bot *)
      replace (Z.of_nat (b-1) + 1)%Z with (Z.of_nat b)...
      wp_bind (_ <- _)%E.

      iInv "Inv" as (γq' γpop' γm' t4 b4 l4 Pop4)
        ">(%Enc & %Bound4 & Phys & Abst & Mono)".
        encode_agree Enc.
      iDestruct "Abst" as "[Q P]".
        iDestruct (ghost_var_agree with "γ👑 P") as "%". subst Pop4.
        iMod (ghost_var_update_2 false with "γ👑 P") as "[γ👑 P]"...
      iCombine "Q P" as "Abst".
      iDestruct "Phys" as "(t↦ & b↦ & arr↦)".
        iDestruct (mapsto_agree with "b↦ b👑") as "%".
          injection H as [=]. assert (b = b4)... subst b4. clear H.
        iDestruct (array_agree with "arr↦ arr👑") as "%"... subst l4.
        iCombine "b👑 b↦" as "b↦". wp_store.
        iDestruct "b↦" as "[b👑 b↦]".
      iCombine "t↦ b↦ arr↦" as "Phys".
      iModIntro. iSplitL "Phys Abst Mono".
      { iExists _,_,_, t4,b,_,false. fr. }
      wp_pures. iApply "Φ". fr.
    - (* fail *)
      iDestruct "Phys" as "(t↦ & b↦ & arr↦)".
        wp_cmpxchg_fail. { intro. injection H... }
      iCombine "t↦ b↦ arr↦" as "Phys".

      iMod "AU" as (l') "[Cont [_ Commit]]".
      iMod ("Commit" $! l' NONEV with "[Cont]") as "Φ"...
      iModIntro. iSplitL "Phys Abst Mono".
        { iExists _,_,_, t3,b,_,true. fr. }
      wp_pures.

      (* store bot *)
      replace (Z.of_nat (b-1) + 1)%Z with (Z.of_nat b)...
      wp_bind (_ <- _)%E.
      iInv "Inv" as (γq' γpop' γm' t4 b4 l4 Pop4)
        ">(%Enc & %Bound4 & Phys & Abst & Mono)".
        encode_agree Enc.
      iDestruct "Abst" as "[Q P]".
        iDestruct (ghost_var_agree with "γ👑 P") as "%". subst Pop4.
        iMod (ghost_var_update_2 false with "γ👑 P") as "[γ👑 P]"...
      iCombine "Q P" as "Abst".
      iDestruct "Phys" as "(t↦ & b↦ & arr↦)".
        iDestruct (mapsto_agree with "b↦ b👑") as "%".
          injection H as [=]. assert (b = b4) by lia. subst b4. clear H.
          iCombine "b👑 b↦" as "b↦". wp_store.
          iDestruct "b↦" as "[b👑 b↦]".
        iDestruct (array_agree with "arr↦ arr👑") as "%"... subst l4.
      iCombine "t↦ b↦ arr↦" as "Phys".

      iModIntro. iSplitL "Phys Abst Mono".
      { iExists _,_,_, t4,b,_,false. fr. }
      wp_pures. iApply "Φ". fr.
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
      iDestruct "Is" as (arr top bot) "[%Is Inv]". subst.
    wp_lam. unfold code.arr, code.top, code.bot. wp_pures.

    (* load top *)
    wp_bind (! _)%E.
      iInv "Inv" as (γq γpop γm t1 b1 l1 Pop1)
        ">(%Enc & %Bound1 & Phys & Abst & Mono)".
      iDestruct "Mono" as (hl1) "[Mono %HistPref1]".
      iDestruct (mono_deque_get_lb with "Mono") as "#Mlb1".
      iDestruct "Phys" as "(t↦ & b↦ & arr↦)". wp_load.
      iCombine "t↦ b↦ arr↦" as "Phys".
    iModIntro. iSplitL "Phys Abst Mono".
      { iExists _,_,_, t1,b1,l1,Pop1. fr. }
    wp_pures.

    (* load bot *)
    wp_bind (! _)%E.
      iInv "Inv" as (γq' γpop' γm' t2 b2 l2 Pop2)
        ">(%Enc' & %Bound2 & Phys & Abst & Mono)".
        encode_agree Enc.
      iDestruct "Mono" as (hl2) "[Mono %HistPref2]".
      iDestruct (mono_deque_get_lb with "Mono") as "#Mlb2".
      iDestruct (mono_deque_auth_lb_top with "Mono Mlb1") as "%Ht12".
      iDestruct "Phys" as "(t↦ & b↦ & arr↦)". wp_load.
      iCombine "t↦ b↦ arr↦" as "Phys".
    iModIntro. iSplitL "Phys Abst Mono".
      { iExists _,_,_, t2,b2,l2,Pop2. fr. }
    wp_pures.

    (* no chance to steal *)
    case_bool_decide; wp_pures.
    { iMod "AU" as (l) "[Cont [_ Commit]]".
      iMod ("Commit" $! l NONEV with "[Cont]") as "Φ"...
      iApply "Φ"... }
    assert (t1 < b2) as Htb12. 1: destruct Pop2... clear H.

    (* read [t1] *)
    wp_bind (! _)%E. rewrite rem_mod_eq...
      iInv "Inv" as (γq' γpop' γm' t3 b3 l3 Pop3)
        ">(%Enc' & %Bound3 & Phys & Abst & Mono)".
        encode_agree Enc.
      iDestruct "Mono" as (hl3) "[Mono %HistPref3]".
        iDestruct (mono_deque_get_lb with "Mono") as "#Mlb3".
        iDestruct (mono_deque_auth_lb_top with "Mono Mlb2") as "%Ht23".
      destruct (mod_get_is_Some l3 t1) as [v Hv]...
      iDestruct "Phys" as "(t↦ & b↦ & arr↦)".
        iApply (wp_load_offset with "arr↦").
        1: { destruct Bound3. rewrite -e... }
        iNext. iIntros "arr↦".
      iCombine "t↦ b↦ arr↦" as "Phys".
    iModIntro. iSplitL "Phys Abst Mono".
      { iExists _,_,_, t3,b3,l3,Pop3. fr. }
    wp_pures.

    (* cas top *)
    wp_bind (CmpXchg _ _ _)%E.
      iInv "Inv" as (γq' γpop' γm' t4 b4 l4 Pop4)
        ">(%Enc' & %Bound4 & Phys & Abst & Mono)".
        encode_agree Enc.
      iDestruct "Mono" as (hl4) "[Mono %HistPref4]".
        iDestruct (mono_deque_get_lb with "Mono") as "#Mlb4".
        iDestruct (mono_deque_auth_lb_top with "Mono Mlb3") as "%Ht34".
    destruct (decide (t1 = t4)).
    - (* success *)
      assert (t1 = t2)... assert (t2 = t3)... subst t1 t2 t3.
        iDestruct (mono_deque_lb_history with "Mlb3") as "%Hist3".
        destruct Hist3 as [NO|[Hist3 Htb3]]...
        iDestruct (mono_deque_lb_history with "Mlb4") as "%Hist4".
        destruct Hist4 as [NO|[Hist4 Htb4]]...
      iDestruct (mono_deque_lb_lookup _ t4 with "Mlb3 Mlb4") as "%H34"...
      assert (mod_get l3 t4 = mod_get l4 t4).
      { apply HistPref3 in Htb3. apply HistPref4 in Htb4.
        rewrite -Htb3 -Htb4... }
        rewrite H in Hv. clear H.
      iDestruct "Phys" as "(t↦ & b↦ & arr↦)".
        wp_cmpxchg_suc.
        replace (Z.of_nat t4 + 1)%Z with (Z.of_nat (S t4))...
      iCombine "t↦ b↦ arr↦" as "Phys".
      destruct (mod_get_is_Some l4 (S t4)) as [v' Hv']...
      iMod (mono_deque_steal _ v' with "Mono") as "Mono"...

      (* AU *)
      iMod "AU" as (l') "[Cont [_ Commit]]".
        iDestruct "Cont" as (γq' γpop' γm') "[%Enc' Cont]".
        encode_agree Enc.
      iDestruct "Abst" as "[Q P]".
        iDestruct (ghost_var_agree with "Cont Q") as "%". subst l'.
        iMod (ghost_var_update_2 (circ_slice l4 (S t4) b4)
          with "Cont Q") as "[Cont Q]"...
      iCombine "Q P" as "Abst".
      iMod ("Commit" $! (circ_slice l4 (S t4) b4) (SOMEV v)
        with "[Cont]") as "Φ".
        { fr. simpl. erewrite <- circ_slice_shrink_left... }
      iModIntro. iSplitL "Phys Abst Mono".
      { iExists _,_,_, (S t4),b4,l4,Pop4. fr. fr.
        iPureIntro; intros. case_decide... rewrite Hv' lookup_app_r...
        replace (S t4 - length hl4) with 0... }
      wp_pures. iApply "Φ"...
    - (* fail *)
      iDestruct "Phys" as "(t↦ & b↦ & arr↦)".
        wp_cmpxchg_fail. { intro. injection H... }
      iCombine "t↦ b↦ arr↦" as "Phys".
      iMod "AU" as (l) "[Cont [_ Commit]]".
        iDestruct "Cont" as (γq' γpop' γm') "[%Enc' Cont]".
        encode_agree Enc.
      iMod ("Commit" $! l NONEV with "[Cont]") as "Φ". 1: fr.
      iModIntro. iSplitL "Phys Abst Mono".
        { iExists _,_,_, t4,b4,l4,Pop4. fr. }
      wp_pures. iApply "Φ"...
  Qed.
End proof.

Program Definition atomic_deque `{!heapGS Σ, !dequeG Σ} :
  spec.atomic_deque Σ :=
  {| spec.new_deque_spec := new_deque_spec;
     spec.push_spec := push_spec;
     spec.pop_spec := pop_spec;
     spec.steal_spec := steal_spec; |}.
(* TODO we have to prove deque_content exclusive.
  use excl auth instead of ghost var 1/2 *)
Next Obligation. Admitted.

Global Typeclasses Opaque deque_content is_deque.

