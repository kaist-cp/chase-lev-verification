From iris.algebra Require Import excl auth list.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import invariants ghost_var mono_nat.
From chase_lev Require Import atomic.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import proofmode notation.
From iris.prelude Require Import options.
From chase_lev Require Import mono_list.
From chase_lev.circular Require Import helpers.

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
- history = [#(), 1, 2, ..., 10, 11, ..., 99, 10, 20]
    where 1 to 3 were erased from the array       ^
                                                  t
Note on history:
- history is the list of "determined elements", i.e.
  those that are definitely the last element pushed at
  each index and won't be overwritten.
- history includes indices from 0 to either t or t-1.
  If t = b, the element at t may be overwritten by push,
  so history goes up to t-1. Otherwise, it goes up to t.
- history[0] is #() because t starts from 1 (because we
  need to reason about t-1). However, this fact is not
  necessary for proof.

Invariants:
- top |-> t
- bot |-> b if "not popping", otherwise bot |-> b-1
- arr |-> l
- those in history are preserved (done by mono_list)
- top always increases (done by mono_nat)
- l and history matches "somehow (TODO)"
*)

Section code.
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
      if: #CAP_CONST ≤ "b" then loop #() else
      "array" +ₗ "b" <- "v" ;;
      bot "deque" <- "b" + #1.
  
  (* TODO: change to NONE/SOME *)
  Definition pop : val :=
    λ: "deque",
      let: "array" := arr "deque" in
      let: "b" := !(bot "deque") - #1 in
      bot "deque" <- "b" ;;
      let: "t" := !(top "deque") in
      if: "b" < "t" then (* empty pop *)
        bot "deque" <- "t" ;; (#false, #())
      else let: "v" := !("array" +ₗ "b") in
      if: "t" < "b" then (#true, "v") (* normal case *)
      else let: "ok" := CAS (top "deque") "t" ("t" + #1) in
      bot "deque" <- "t" + #1 ;;
      if: "ok" then (#true, "v") (* popped *)
      else (#false, #()). (* stolen *)

  (* NOTE: b ≤ t doesn't necessarily mean the deque was empty!
    It can also be the case that there was one element and
    the owner thread prematurely decremented b trying to pop. *)
  (* TODO: change to NONE/SOME *)
  Definition steal : val :=
    λ: "deque",
      let: "array" := arr "deque" in
      let: "t" := !(top "deque") in
      let: "b" := !(bot "deque") in
      if: "b" ≤ "t" then (#false, #()) (* too small to steal *)
      else let: "v" := !("array" +ₗ "t") in
      if: CAS (top "deque") "t" ("t" + #1)
      then (#true, "v") (* success *)
      else (#false, #()). (* fail *)
End code.

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
    mono_list_auth_own γl 1 hl ∗
    mono_nat_auth_own γt 1 t ∗
    ⌜(length hl = t ∧ t = b) ∨ (length hl = S t ∧ t < b)⌝.

  Definition mono_deque_lb_own (γm : gname) (hl : list val) (t b : nat) : iProp :=
    ∃ (γl γt : gname),
    ⌜γm = encode (γl, γt)⌝ ∗
    mono_list_lb_own γl hl ∗
    mono_nat_lb_own γt t ∗
    ⌜(length hl = t ∧ t = b) ∨ (length hl = S t ∧ t < b)⌝.
(*
  Lemma mono_deque_own_alloc l :
    ⌜length l = CAP_CONST⌝ ==∗ ∃ γ, mono_deque_auth_own γ l 1 1.
  Proof.
    iIntros (H).
    iMod (mono_list_own_alloc (take 1 l)) as (γl) "[L _]".
    iMod (mono_nat_own_alloc 1) as (γtb) "[N _]".
    iExists (encode (γl, γtb)). iModIntro.
    iExists _,_. iSplit; iFrame; auto.
    iPureIntro. unfold CAP_CONST. split; auto. lia.
  Qed.

  Lemma mono_deque_definite_length γm l t b :
    mono_deque_lb_own γm l t b -∗ ⌜definite t b ≤ b ≤ length l⌝.
  Proof.
    iIntros  "(%γl & %γtb & %ENC & [%BOUND1 %BOUND2] & L & N)".
    unfold definite. case_decide; iPureIntro; try lia.
  Qed.

  Lemma mono_deque_auth_insert γm l t b i v :
    (definite t b) ≤ i →
    mono_deque_auth_own γm l t b -∗
    mono_deque_auth_own γm (<[i:=v]> l) t b.
  Proof.
    iIntros (H) "(%γl & %γtb & %ENC & %BOUND & L & N)".
    iExists _,_. repeat iSplit; auto. all: try iPureIntro; try lia.
    1: rewrite insert_length; lia.
    rewrite take_insert; auto. iFrame.
  Qed.
*)
  Lemma mono_deque_lb_history γm l t b :
    mono_deque_lb_own γm l t b -∗
    ⌜(length l = t ∧ t = b) ∨ (length l = S t ∧ t < b)⌝.
  Proof. iIntros "(%γl & %γt & %ENC & L & N & %BOUND)". auto. Qed.

  Lemma mono_deque_lb_lookup γm i l1 t1 b1 l2 t2 b2 :
    i < length l1 → i < length l2 →
    mono_deque_lb_own γm l1 t1 b1 -∗ mono_deque_lb_own γm l2 t2 b2 -∗
    ⌜l1 !! i = l2 !! i⌝.
  Proof.
    iIntros (Hi Hv).
    iIntros "(%γl & %γt & %ENC1 & L1 & N1 & %BOUND1)".
    iIntros "(%γl' & %γt' & %ENC2 & L2 & N2 & %BOUND2)".
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
    iIntros "(%γl & %γt & %ENC & L & N & %BOUND)".
    iDestruct (mono_list_lb_own_get with "L") as "#Llb".
    iDestruct (mono_nat_lb_own_get with "N") as "#Nlb".
    iExists _,_. repeat iSplit; auto.
  Qed.

  Lemma mono_deque_auth_lb_length γm l1 t1 b1 l2 t2 b2 :
    mono_deque_auth_own γm l1 t1 b1 -∗ mono_deque_lb_own γm l2 t2 b2 -∗
    ⌜length l2 ≤ length l1⌝.
  Proof.
    iIntros "(%γl & %γt & %ENC1 & L1 & N1 & %BOUND1)".
    iIntros "(%γl' & %γt' & %ENC2 & L2 & N2 & %BOUND2)".
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
    iDestruct "D1" as "(%γl & %γt & %ENC1 & L1 & N1 & %BOUND1)".
    iDestruct "D2" as "(%γl' & %γt' & %ENC2 & L2 & N2 & %BOUND2)".
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
    iIntros (H) "(%γl & %γt & %ENC & L & N & %BOUND)".
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
    iIntros (H HU) "(%γl & %γt & %ENC & L & N & %BOUND)".
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
    iIntros (H1 H2) "(%γl & %γt & %ENC & L & N & %BOUND)".
    destruct BOUND as [[Hl1 Hb]|[Hl1 Hb]]; try lia.
    iExists _,_. repeat iSplit; auto; iFrame.
    iPureIntro. lia.
  Qed.
End RA.

Section proof.
  Context `{!heapGS Σ, !dequeG Σ} (N : namespace).
  Notation iProp := (iProp Σ).

  (* TODO: change l to ↦∗{#1} & make another ghost_var in deque_content?
     (see msqueue) *)
  Definition deque_inv (γ : gname) (arr top bot : loc) : iProp :=
    ∃ (γq γpop γm : gname) (t b : nat) (l : list val) (Popping : bool),
      ⌜γ = encode (γq, γpop, γm)⌝ ∗
      ⌜1 ≤ t ≤ b ≤ CAP_CONST ∧ length l = CAP_CONST⌝ ∗
      (* physical state *)
      ( let bp := if Popping then b-1 else b in
        top ↦ #t ∗ bot ↦{#1/2} #bp ∗ arr ↦∗{#1/2} l
      ) ∗
      (* abstract state *)
      ( ghost_var γq (1/2) (slice l t b) ∗
        ghost_var γpop (1/2) Popping
      ) ∗
      (* monotonicity *)
      ∃ (hl : list val), mono_deque_auth_own γm hl t b.

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

  Ltac fr :=
    repeat iExists _;
    try iFrame "arr↦"; try iFrame "arr↦1"; try iFrame "arr↦2"; 
    iFrame; eauto.
  Ltac autoall :=
    eauto;
    unfold CAP_CONST in *; unfold helpers.CAP_CONST in *;
    (*unfold definite;*)
    try by (
      repeat iNext; repeat iIntros; repeat intros;
      try case_decide; try iPureIntro;
      try rewrite lookup_lt_is_Some;
      try rewrite Qp.half_half;
      try lia; done
    ).

(*
  Lemma new_deque_spec :
    {{{ True }}}
      new_deque #()
    {{{ γq γpop γm q, RET q;
      is_deque γq γpop γm q ∗ deque_content γq [] ∗
      own_deque γq γpop q
    }}}.
  Proof with autoall.
    iIntros (Φ) "_ HΦ".
    wp_lam. wp_alloc arr as "[arr↦1 arr↦2]"...
    wp_pures. wp_alloc b as "[b↦1 b↦2]". wp_alloc t as "t↦".
    iMod (ghost_var_alloc []) as (γq) "[γq1 γq2]".
    iMod (ghost_var_alloc false) as (γpop) "[γpop1 γpop2]".
    iMod (mono_deque_own_alloc (replicate (Z.to_nat CAP_CONST) #0)
      with "[]") as (γm) "γm"...
    iMod (inv_alloc N _ (deque_inv γq γpop γm arr t b)
      with "[t↦ b↦1 arr↦1 γq1 γpop1 γm]") as "Inv".
    { fr. rewrite replicate_length... }
    wp_pures. iModIntro. iApply "HΦ". iSplit; fr.
    iExists _,_,_,1,_. fr.
  Qed.
*)
  Lemma push_spec γ q (v : val) :
    is_deque γ q -∗
    own_deque γ q -∗
    <<< ∀∀ l : list val, deque_content γ l >>>
      push q v @ ↑N
    <<< deque_content γ (l ++ [v]),
      RET #(), own_deque γ q >>>.
  Proof with autoall.
    iIntros "#Is Own" (Φ) "AU".
      iDestruct "Own" as (γq γpop γm arr top bot b l)
        "(%Hγ & -> & %HL & γ👑 & b👑 & arr👑)".
      iDestruct "Is" as (arr' top' bot') "[%Is Inv]".
      injection Is as [= <- <- <-].
    wp_lam. unfold code.arr, code.bot. wp_pures.

    (* load bot *)
    wp_load. wp_pures.
    case_bool_decide as HbC. { wp_pures. iApply loop_spec... }
    wp_pures.

    (* store value *)
    wp_bind (_ <- _)%E.
      iInv "Inv" as (γq' γpop' γm' t1 b1 l1 Pop1)
        ">(%Enc & %Bound1 & Phys & Abst & Mono)".
        encode_agree Enc.
      iDestruct "Abst" as "[Q P]".
        iDestruct (ghost_var_agree with "γ👑 P") as "%". subst Pop1.
      iCombine "Q P" as "Abst".
      iDestruct "Phys" as "(t↦ & b↦ & arr↦)".
        iDestruct (mapsto_agree with "b↦ b👑") as "%".
          injection H as [=]. apply Nat2Z.inj in H. subst b1.
        iDestruct (array_agree with "arr↦ arr👑") as "%"... subst l1.
        iCombine "arr↦ arr👑" as "arr↦".
        iApply (wp_store_offset with "arr↦")...
        iNext. iIntros "[arr↦ arr👑]".
      iCombine "t↦ b↦ arr↦" as "Phys".
      iModIntro. iSplitL "Phys Abst Mono".
      { iExists _,_,_, _,_,(<[b:=v]>l),_.
        rewrite insert_length. rewrite slice_insert_right...
        iSplit... iSplit... fr. }
    wp_pures.
    replace (Z.of_nat b + 1)%Z with (Z.of_nat (S b))...

    (* store bot *)
    iInv "Inv" as (γq' γpop' γm' t2 b2 l2 Pop2)
        ">(%Enc & %Bound2 & Phys & Abst & Mono)".
        encode_agree Enc.
      iMod "AU" as (q) "[Cont [_ Commit]]".
        iDestruct "Cont" as (γq' γpop' γm') "[%Enc Cont]".
        encode_agree Enc.
      iDestruct "Abst" as "[Q P]".
        iDestruct (ghost_var_agree with "Q Cont") as "%". subst q.
        iMod (ghost_var_update_2 (slice (<[b:=v]> l) t2 (S b))
          with "Q Cont") as "[Q Cont]"...
        iDestruct (ghost_var_agree with "γ👑 P") as "%". subst Pop2.
      iCombine "Q P" as "Abst".
      iDestruct "Phys" as "(t↦ & b↦ & arr↦)".
        iDestruct (mapsto_agree with "b↦ b👑") as "%".
          injection H as [=H]. apply Nat2Z.inj in H. subst b2.
        iDestruct (array_agree with "arr↦ arr👑") as "%".
          1: rewrite insert_length... subst l2.
        iCombine "b↦ b👑" as "b↦". wp_store.
        iDestruct "b↦" as "[b↦ b👑]".
      iCombine "t↦ b↦ arr↦" as "Phys".
      iDestruct "Mono" as (hl) "Mono".
        iMod (mono_deque_push _
          (if decide (t2 = b) then hl ++ [v] else hl)
          (S b) with "Mono") as "Mono"...
        { destruct (decide (t2 = b))... right; split... }
      rewrite <- slice_extend_right... 2: rewrite list_lookup_insert...
      iMod ("Commit" with "[Cont]") as "Φ". 1: fr.
    iModIntro. iModIntro.

    iSplitL "Phys Abst Mono".
    { iExists _,_,_, t2,(S b),(<[b:=v]> l),_.
      iSplit... iSplit... fr. }
    iApply "Φ". fr. fr... iSplit... iSplit...
  Qed.

  Lemma pop_spec γ q :
    is_deque γ q -∗
    own_deque γ q -∗
    <<< ∀∀ l : list val, deque_content γ l >>>
      pop q @ ↑N
    <<< ∃∃ (l' : list val) (b : bool) (v : val),
        deque_content γ l' ∗
        ⌜l = if b then l'++[v] else l'⌝ ,
      RET (#b, v), own_deque γ q >>>.
  Proof with autoall.
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
      { iExists _,_,_, t1,b,_,_... repeat iSplit... fr. }
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
      assert (is_Some (l !! (b-1))) as [v Hv]...
        erewrite slice_shrink_right...
      iDestruct "Phys" as "(t↦ & b↦ & arr↦)". wp_load.
      iCombine "t↦ b↦ arr↦" as "Phys".
      iDestruct "Abst" as "[Q P]".
        iDestruct (ghost_var_agree with "Cont Q") as "%". subst l'.
        iMod (ghost_var_update_2 (slice l t2 (b-1)) with "Cont Q")
          as "[Cont Q]"...
        iMod (ghost_var_update_2 false with "γ👑 P") as "[γ👑 P]"...
      iCombine "Q P" as "Abst".
      iDestruct "Mono" as (hl) "Mono".
        iDestruct (mono_deque_pop _ (b-1) with "Mono") as "Mono"...
      iMod ("Commit" $! (slice l t2 (b-1)) true v with "[Cont]") as "Φ".
      { iSplit... fr. }
      iModIntro. iModIntro.
      
      iSplitL "Phys Abst Mono".
      { iExists _,_,_, t2,(b-1),l,false. iSplit... iSplit... fr. }
      wp_pures. case_bool_decide... wp_pures.

      (* read [b2-1] *)
      wp_bind (! _)%E.
      iApply (wp_load_offset with "arr👑")... iNext. iIntros "arr👑".
      wp_pures. case_bool_decide... wp_pures. iApply "Φ". fr. }

    (* otherwise... *)
    iDestruct "Phys" as "(t↦ & b↦ & arr↦)". wp_load.
    iCombine "t↦ b↦ arr↦" as "Phys".
    iModIntro. iSplitL "Phys Abst Mono".
    { iExists _,_,_, t2,b,_,true... repeat iSplit... fr. }
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
      iMod ("Commit" $! l' false #() with "[Cont]") as "Φ"...
      iModIntro. iSplitL "Phys Abst Mono".
      { iExists _,_,_, t3,b,_,false... repeat iSplit... fr. }
      wp_pures. iApply "Φ". fr. }
    
    (* read [b2-1] *)
    wp_bind (! _)%E.
    assert (is_Some (l !! (b-1))) as [v Hv]...
    iApply (wp_load_offset with "arr👑")... iNext. iIntros "arr👑".
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
        erewrite slice_shrink_left... rewrite slice_to_nil...
        iMod (ghost_var_update_2 [] with "Cont Q") as "[Cont Q]"...
      iCombine "Q P" as "Abst".
      iMod ("Commit" $! [] true v with "[Cont]") as "Φ".
        { iSplit... fr. }
      iDestruct "Mono" as (hl) "Mono".
        iMod (mono_deque_pop_singleton _ _ (b-1) with "[Mono]") as "Mono".
        { replace (S (b-1)) with b... }
      replace (S (b-1)) with b...
      iModIntro. iSplitL "Phys Abst Mono".
        { iExists _,_,_, b,b,_,true. repeat iSplit...
          rewrite slice_to_nil... fr. }
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
      { iExists _,_,_, t4,b,_,false. repeat iSplit... fr. }
      wp_pures. iApply "Φ". fr.
    - (* fail *)
      iDestruct "Phys" as "(t↦ & b↦ & arr↦)".
        wp_cmpxchg_fail. { intro. injection H... }
      iCombine "t↦ b↦ arr↦" as "Phys".

      iMod "AU" as (l') "[Cont [_ Commit]]".
      iMod ("Commit" $! l' false #() with "[Cont]") as "Φ"...
      iModIntro. iSplitL "Phys Abst Mono".
        { iExists _,_,_, t3,b,_,true. repeat iSplit... fr. }
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
      { iExists _,_,_, t4,b,_,false. repeat iSplit... fr. }
      wp_pures. iApply "Φ". fr.
  Qed.

  Lemma steal_spec γ q :
    is_deque γ q -∗
    <<< ∀∀ l : list val, deque_content γ l >>>
      steal q @ ↑N
    <<< ∃∃ (l' : list val) (b : bool) (v : val),
        deque_content γ l' ∗
        ⌜l = if b then [v]++l' else l'⌝ ,
      RET (#b, v) >>>.
  Proof with autoall.
    iIntros "#Is" (Φ) "AU".
      iDestruct "Is" as (arr top bot) "[%Is Inv]". subst.
    wp_lam. unfold code.arr, code.top, code.bot. wp_pures.

    (* load top *)
    wp_bind (! _)%E.
      iInv "Inv" as (γq γpop γm t1 b1 l1 Pop1)
        ">(%Enc & %Bound1 & Phys & Abst & [%hl1 Mono])".
      iDestruct (mono_deque_get_lb with "Mono") as "#Mlb1".
      iDestruct "Phys" as "(t↦ & b↦ & arr↦)". wp_load.
      iCombine "t↦ b↦ arr↦" as "Phys".
    iModIntro. iSplitL "Phys Abst Mono".
      { iExists _,_,_, t1,b1,l1,Pop1. repeat iSplit... fr. }
    wp_pures.

    (* load bot *)
    wp_bind (! _)%E.
      iInv "Inv" as (γq' γpop' γm' t2 b2 l2 Pop2)
        ">(%Enc' & %Bound2 & Phys & Abst & [%hl2 Mono])".
        encode_agree Enc.
      iDestruct (mono_deque_get_lb with "Mono") as "#Mlb2".
      iDestruct (mono_deque_auth_lb_top with "Mono Mlb1") as "%Ht12".
      iDestruct "Phys" as "(t↦ & b↦ & arr↦)". wp_load.
      iCombine "t↦ b↦ arr↦" as "Phys".
    iModIntro. iSplitL "Phys Abst Mono".
      { iExists _,_,_, t2,b2,l2,Pop2. repeat iSplit... fr. }
    wp_pures.

    (* no chance to steal *)
    case_bool_decide; wp_pures.
    { iMod "AU" as (l) "[Cont [_ Commit]]".
      iMod ("Commit" $! l false #() with "[Cont]") as "Φ"...
      iApply "Φ"... }
    assert (t1 < b2) as Htb12. 1: destruct Pop2... clear H.

    (* read [t1] *)
    wp_bind (! _)%E.
      iInv "Inv" as (γq' γpop' γm' t3 b3 l3 Pop3)
        ">(%Enc' & %Bound3 & Phys & Abst & [%hl3 Mono])".
        encode_agree Enc.
      iDestruct (mono_deque_get_lb with "Mono") as "#Mlb3".
      iDestruct (mono_deque_auth_lb_top with "Mono Mlb2") as "%Ht23".
      assert (is_Some (l3 !! t1)) as [v Hv]...
      iDestruct "Phys" as "(t↦ & b↦ & arr↦)".
        iApply (wp_load_offset with "arr↦")... iNext. iIntros "arr↦".
      iCombine "t↦ b↦ arr↦" as "Phys".
    iModIntro. iSplitL "Phys Abst Mono".
      { iExists _,_,_, t3,b3,l3,Pop3. repeat iSplit... fr. }
    wp_pures.

    (* cas top *)
    wp_bind (CmpXchg _ _ _)%E.
      iInv "Inv" as (γq' γpop' γm' t4 b4 l4 Pop4)
        ">(%Enc' & %Bound4 & Phys & Abst & [%hl4 Mono])".
        encode_agree Enc.
      iDestruct (mono_deque_get_lb with "Mono") as "#Mlb4".
      iDestruct (mono_deque_auth_lb_top with "Mono Mlb3") as "%Ht34".
    destruct (decide (t1 = t4)).
    - (* success *)
      assert (t1 = t2)... assert (t2 = t3)... subst t1 t2 t3.
        iDestruct (mono_deque_lb_history with "Mlb3") as "%Hist3".
        destruct Hist3 as [NO|[Hist3 Htb3]]...
        iDestruct (mono_deque_lb_history with "Mlb4") as "%Hist4".
        destruct Hist4 as [NO|[Hist4 Htb4]]...
      iDestruct "Phys" as "(t↦ & b↦ & arr↦)".
        wp_cmpxchg_suc.
        replace (Z.of_nat t4 + 1)%Z with (Z.of_nat (S t4))...
      iCombine "t↦ b↦ arr↦" as "Phys".
      iDestruct (mono_deque_lb_lookup _ t4 with "Mlb3 Mlb4") as "%"...
      iMod (mono_deque_steal with "Mono") as "Mono"...

      (* AU *)
      iMod "AU" as (l') "[Cont [_ Commit]]".
        iDestruct "Cont" as (γq' γpop' γm') "[%Enc' Cont]".
        encode_agree Enc.
      iDestruct "Abst" as "[Q P]".
        iDestruct (ghost_var_agree with "Cont Q") as "%". subst l'.
        iMod (ghost_var_update_2 (slice l4 (S t4) b4)
          with "Cont Q") as "[Cont Q]"...
      iCombine "Q P" as "Abst".
      iMod ("Commit" $! (slice l4 (S t4) b4) true v with "[Cont]") as "Φ".
        { iSplit. 1: fr. simpl.
          erewrite <- slice_shrink_left... admit. }
      iModIntro. iSplitL "Phys Abst Mono".
        { iExists _,_,_, (S t4),b4,l4,Pop4. repeat iSplit... fr. }
      wp_pures. iApply "Φ"...
    - (* fail *)
      iDestruct "Phys" as "(t↦ & b↦ & arr↦)".
        wp_cmpxchg_fail. { intro. injection H... }
      iCombine "t↦ b↦ arr↦" as "Phys".
      iMod "AU" as (l) "[Cont [_ Commit]]".
        iDestruct "Cont" as (γq' γpop' γm') "[%Enc' Cont]".
        encode_agree Enc.
      iMod ("Commit" $! l false #() with "[Cont]") as "Φ".
        { iSplit... fr. }
      iModIntro. iSplitL "Phys Abst Mono".
        { iExists _,_,_, t4,b4,l4,Pop4. repeat iSplit... fr. }
      wp_pures. iApply "Φ"...
  Qed.
End proof.
