From iris.algebra Require Import list excl_auth.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import invariants ghost_var ghost_map mono_nat.
From chase_lev Require Import mono_list atomic.
From iris.heap_lang Require Import proofmode notation.
From iris.prelude Require Import options.
From chase_lev.circular2 Require Import helpers code_circle.

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

Invariants:
- top |-> t
- bot |-> b if "not popping", otherwise bot |-> b-1
- arr |-> l
- those in history are preserved (done by mono_list)
- top always increases (done by mono_nat)
- l and history matches at top
*)

Section code.
  Definition new_deque : val :=
    λ: "sz",
      let: "array" := new_circle "sz" in
      (ref "array", ref #1, ref #1). (* array+size, top, bot *)
  
  Definition arr : val := λ: "deque", Fst (Fst "deque").
  Definition top : val := λ: "deque", Snd (Fst "deque").
  Definition bot : val := λ: "deque", Snd "deque".
(*
  Definition push : val :=
    rec: "push" "deque" "v" :=
      let: "arraysz" := !(arr "deque") in
      let: "array" := Fst "arraysz" in
      let: "sz" := Snd "arraysz" in
      let: "b" := !(bot "deque") in
      if: !(top "deque") + "sz" ≤ "b"
        then "push" "deque" "v"
      else
      "array" +ₗ ("b" `rem` "sz") <- "v" ;;
      bot "deque" <- "b" + #1.
  
  Definition pop : val :=
    λ: "deque",
      let: "arraysz" := !(arr "deque") in
      let: "array" := Fst "arraysz" in
      let: "sz" := Snd "arraysz" in
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
*)
  (* NOTE: b ≤ t doesn't necessarily mean the deque was empty!
    It can also be the case that there was one element and
    the owner thread decremented b trying to pop. *)
  Definition steal : val :=
    λ: "deque",
      let: "t" := !(top "deque") in
      let: "b" := !(bot "deque") in
      let: "array" := AllocN #1 #0 in
      "array" <- !(arr "deque") ;;
      if: "b" ≤ "t" then NONE (* no chance *)
      else let: "v" := get_circle !"array" "t" in
      if: CAS (top "deque") "t" ("t" + #1)
      then SOME "v" (* success *)
      else NONE. (* fail *)
End code.

(** Ghost state for the deque *)

Class dequeG Σ := DequeG {
    deque_tokG :> inG Σ (excl_authR $ listO valO);
    deque_popG :> ghost_varG Σ bool;
    mono_listG :> mono_listG val Σ;
    mono_natG :> mono_natG Σ;
    all_arraysG :> ghost_mapG Σ gname (list val)
  }.

Definition dequeΣ : gFunctors :=
  #[GFunctor (excl_authR $ listO valO);
    ghost_varΣ bool;
    mono_listΣ val;
    mono_natΣ;
    ghost_mapΣ gname (list val)
  ].

Global Instance subG_dequeΣ {Σ} : subG dequeΣ Σ → dequeG Σ.
Proof. solve_inG. Qed.
(*
(* we wrap monotonicity for easier reasoning *)
Section monotone_ghost.
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
End monotone_ghost.
*)
Section proof.
  Context `{!heapGS Σ, !dequeG Σ, !circleG Σ} (N : namespace).
  Notation iProp := (iProp Σ).

  Let circleN := N .@ "circle".
  Let dequeN := N .@ "deque".

  Definition all_arrays (γm γcur : gname) : iProp :=
    ∃ (garrs : gmap gname (list val)),
    ⌜γcur ∈ dom garrs⌝ ∗
    ghost_map_auth γm 1 garrs ∗
    [∗ map] γ ↦ l ∈ garrs,
      ⌜γ = γcur⌝ ∨ circle_content γ l.
      (* TODO: it should be circle_persistent_content! *)

  Definition deque_inv (γq γpop γm : gname) (A top bot : loc) : iProp :=
    ∃ (l : list val) (t b : nat),
      ⌜1 ≤ t ≤ b⌝ ∗
      (* circular array *)
      ( ∃ (γC : gname) (ca : val),
        A ↦{#1/2} ca ∗ 
        is_circle circleN γC ca ∗ circle_content γC l ∗
        all_arrays γm γC
      ) ∗
      (* top *)
      top ↦ #t ∗
      (* bottom *)
      ( ∃ (Popping : bool),
        let bp := if Popping then b-1 else b in
        bot ↦{#1/2} #bp ∗
        ghost_var γpop (1/2) Popping
      ) ∗
      (* logical data *)
      ( own γq (●E (circ_slice l t b)) ∗
        ( ∃ (hl : list val),
          True ∗ (*mono_deque_auth_own γmono hl t b ∗*)
          True (*⌜t < b → hl !! t = mod_get l t⌝*)
        )
      ).

  Definition is_deque (γ : gname) (q : val) : iProp :=
    ∃ (γq γpop γm : gname) (A top bot : loc),
      ⌜q = (#A, #top, #bot)%V⌝ ∗
      ⌜γ = encode (γq, γpop, γm)⌝ ∗
      inv dequeN (deque_inv γq γpop γm A top bot).
  Global Instance is_deque_persistent γ q :
    Persistent (is_deque γ q) := _.

  Definition deque_content (γ : gname) (frag : list val) : iProp :=
    ∃ (γq γpop γm : gname),
      ⌜γ = encode (γq, γpop, γm)⌝ ∗
      own γq (◯E frag).

  (* owner of the deque who can call push and pop *)
  Definition own_deque (γ : gname) (q : val) : iProp :=
    ∃ (γq γpop γm : gname) (ca : val) (A top bot : loc) (b : nat),
      ⌜γ = encode (γq, γpop, γm)⌝ ∗
      ⌜q = (#A, #top, #bot)%V⌝ ∗
      (* own circle *)
      A ↦{#1/2} ca ∗ own_circle ca ∗
      (* own bottom *)
      bot ↦{#1/2} #b ∗ ghost_var γpop (1/2) false.
  
  Ltac extended_auto :=
    eauto;
    try rewrite Nat2Z.id;
    try rewrite replicate_length;
    try rewrite Qp.half_half;
    try by (
      repeat iNext; repeat iIntros; repeat intros;
      try case_decide; try iPureIntro;
      try rewrite lookup_lt_is_Some;
      try lia; done
    ).
  Ltac fr :=
    repeat iSplit; extended_auto; repeat iExists _;
    try iFrame "arr↦"; try iFrame "arr↦1"; try iFrame "arr↦2"; 
    iFrame; eauto.

  Lemma deque_content_exclusive γ frag1 frag2 :
    deque_content γ frag1 -∗ deque_content γ frag2 -∗ False.
  Proof.
    iIntros "C1 C2".
      iDestruct "C1" as (γC γq γpop γm) "[%Enc C1]".
      iDestruct "C2" as (γC' γq' γpop' γm') "[%Enc' C2]".
      encode_agree Enc.
    by iDestruct (own_valid_2 with "C1 C2") as %?%auth_frag_op_valid_1.
  Qed.

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
    wp_bind (new_circle _)%E.
    iApply (new_circle_spec circleN)...
    iIntros (γC ca l) "!> (%Len & IC & 🎯 & Ⓜ️)". wp_pures.
    wp_alloc bot as "[b↦1 b↦2]". wp_alloc top as "t↦".
    wp_alloc A as "[A↦1 A↦2]". wp_pures.

    (* make resources *)
    iMod (own_alloc (●E [] ⋅ ◯E [])) as (γq) "[γq● γq◯]".
      1: apply excl_auth_valid.
    iMod (ghost_var_alloc false) as (γpop) "[γpop1 γpop2]".
    iMod (ghost_map_alloc {[γC:=nil]}) as (γm) "[γm elems]".
    iMod (inv_alloc dequeN _ (deque_inv γq γpop γm A top bot)
      with "[A↦1 t↦ b↦1 IC 🎯 γq● γpop1 γm]") as "Inv".
    { iExists l, 1, 1. fr.
      iSplitL "A↦1 IC 🎯 γm"; fr. fr.
      rewrite dom_singleton elem_of_singleton big_sepM_singleton...
    }

    (* apply Φ *)
    iApply "HΦ". iModIntro. iSplitL "Inv"; first fr.
    iSplitL "γq◯"; first fr. fr. fr. instantiate (1:=1)...
  Qed.
(*
  Lemma push_spec γ q (v : val) :
    is_deque γ q -∗
    own_deque γ q -∗
    <<< ∀∀ l : list val, deque_content γ l >>>
      push q v @ ↑N
    <<< deque_content γ (l ++ [v]),
      RET #(), own_deque γ q >>>.
  Proof with extended_auto.
    iIntros "#Inv Own" (Φ) "AU".
      iLöb as "IH".
      iDestruct "Own" as (γq γpop γm l A arr top bot b)
        "(%Enc & -> & γOwn & AOwn & arrOwn & bOwn)".
      iDestruct "Inv" as (A' top' bot') "[%Q Inv]".
      injection Q as [= <- <- <-].
    wp_lam. unfold code.arr, code.top, code.bot. wp_pures.

    (* load A & bot *)
    wp_load. wp_pures.
    wp_load. wp_pures.

    (* load top *)
    wp_bind (! _)%E.
      iInv "Inv" as (γq' γpop' γm' l1 Pop1 arr1 t1 b1)
        ">(%Enc' & %Bound1 & Phys & Abst & Mono)".
        encode_agree Enc.
      iDestruct "Abst" as "[● P]".
        iDestruct (ghost_var_agree with "γOwn P") as "%". subst Pop1.
      iCombine "● P" as "Abst".
      iDestruct "Phys" as "(A↦ & arr↦ & t↦ & b↦)".
        wp_load.
        iDestruct (mapsto_agree with "A↦ AOwn") as "%HA".
          injection HA as [= -> Hsz].
        iDestruct (mapsto_agree with "b↦ bOwn") as "%Hb".
          injection Hb as [=Hb]. apply Nat2Z.inj in Hb. subst b1.
        iDestruct (array_agree with "arr↦ arrOwn") as "%"... subst l1.
        clear Hsz.
      iCombine "A↦ arr↦ t↦ b↦" as "Phys".
      iDestruct "Mono" as (hl) "[Mono %HistPref1]".
        iDestruct (mono_deque_get_lb with "Mono") as "#Mlb1".
    iModIntro. iSplitL "Phys Abst Mono".
      { iExists _,_,_, l,_,arr. fr. fr. }
    wp_pures.

    (* recurse *)
    case_bool_decide as HbC.
      { wp_pures. iApply ("IH" with "[γOwn AOwn arrOwn bOwn]")...
        iExists _,_,_, l. fr. }
    iClear "IH".
    wp_pures. rewrite rem_mod_eq...

    (* store value *)
    wp_bind (_ <- _)%E.
      iInv "Inv" as (γq' γpop' γm' l2 Pop2 arr2 t2 b2)
        ">(%Enc' & %Bound2 & Phys & Abst & Mono)".
        encode_agree Enc.
      iDestruct "Abst" as "[● P]".
        iDestruct (ghost_var_agree with "γOwn P") as "%". subst Pop2.
      iCombine "● P" as "Abst".
      iDestruct "Phys" as "(A↦ & arr↦ & t↦ & b↦)".
        iDestruct (mapsto_agree with "A↦ AOwn") as "%HA".
          injection HA as [= -> Hsz].
        iDestruct (mapsto_agree with "b↦ bOwn") as "%Hb".
          injection Hb as [=Hb]. apply Nat2Z.inj in Hb. subst b2.
        iDestruct (array_agree with "arr↦ arrOwn") as "%"... subst l2.
        clear Hsz.
        iCombine "arr↦ arrOwn" as "arr↦".
          iApply (wp_store_offset with "arr↦"). 1: apply mod_get_is_Some...
          replace (<[b `mod` length l:=v]> l) with (mod_set l b v)...
        iNext. iIntros "[arr↦ arrOwn]".
      iCombine "A↦ arr↦ t↦ b↦" as "Phys".
      iDestruct "Mono" as (hl1) "[Mono %HistPref2]".
        iDestruct (mono_deque_auth_history with "Mono") as "%Hist2".
      iDestruct (mono_deque_auth_lb_top with "Mono Mlb1") as "%Ht12".
      iModIntro. iSplitL "Phys Abst Mono".
      { iExists _,_,_, (mod_set l b v),false,arr,t2,b.
        rewrite insert_length circ_slice_update_right... fr. fr.
        iIntros "!> %Ht2b". rewrite mod_set_get_ne...
        assert (t2 `mod` length l ≠ b `mod` length l)...
        apply close_mod_neq... }
    wp_pures.
    replace (Z.of_nat b + 1)%Z with (Z.of_nat (S b))...

    (* store bot *)
    iInv "Inv" as (γq' γpop' γm' l3 Pop3 arr3 t3 b3)
        ">(%Enc' & %Bound3 & Phys & Abst & Mono)".
        encode_agree Enc.
      iMod "AU" as (q) "[Cont [_ Commit]]".
        iDestruct "Cont" as (γq' γpop' γm') "[%Enc' ◯]".
        encode_agree Enc.
      iDestruct "Abst" as "[● P]".
        iDestruct (own_ea_agree with "● ◯") as "%". subst q.
        iMod (own_ea_update (circ_slice l3 t3 (S b)) with "● ◯") as "[● ◯]".
        iDestruct (ghost_var_agree with "γOwn P") as "%". subst Pop3.
      iCombine "● P" as "Abst".
      iDestruct "Phys" as "(A↦ & arr↦ & t↦ & b↦)".
        iDestruct (mapsto_agree with "A↦ AOwn") as "%HA".
          injection HA as [= -> Hsz].
        iDestruct (mapsto_agree with "b↦ bOwn") as "%Hb".
          injection Hb as [=Hb]. apply Nat2Z.inj in Hb. subst b3.
        iDestruct (array_agree with "arr↦ arrOwn") as "%".
          1: rewrite insert_length... subst l3.
        iCombine "b↦ bOwn" as "b↦". wp_store.
        iDestruct "b↦" as "[b↦ bOwn]".
      iCombine "A↦ arr↦ t↦ b↦" as "Phys".
      iDestruct "Mono" as (hl3) "[Mono %HistPref3]".
        iDestruct (mono_deque_auth_history with "Mono") as "%Hist3".
        iMod (mono_deque_push _
          (if decide (t3 = b) then hl3 ++ [v] else hl3)
          (S b) with "Mono") as "Mono"...
        { destruct (decide (t3 = b))... right. split... }
      rewrite <- circ_slice_extend_right... 2: rewrite mod_set_get...
      iMod ("Commit" with "[◯]") as "Φ". 1: fr.
    iModIntro. iModIntro.

    iSplitL "Phys Abst Mono".
    { iExists _,_,_, (mod_set l b v),false,_,t3,(S b). iFrame. fr.
      case_decide.
      - subst. destruct Hist3 as [[Hist3 _]|NO]...
        rewrite lookup_app_r... rewrite mod_set_get...
        rewrite Hist3. replace (b-b) with 0...
      - iPureIntro; intros. apply HistPref3... }
    iApply "Φ". iExists _,_,_, (mod_set l b v). fr. fr.
    rewrite Hsz...
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
    iIntros "#Inv Own" (Φ) "AU".
      iDestruct "Own" as (γq γpop γm l A arr top bot b)
        "(%Enc & -> & γOwn & AOwn & arrOwn & bOwn)".
      iDestruct "Inv" as (A' top' bot') "[%Q Inv]".
      injection Q as [= <- <- <-].
    wp_lam. unfold code.arr, code.top, code.bot. wp_pures.

    (* load arr & bot *)
    wp_load. wp_pures.
    wp_load. wp_pures.

    (* decrement b early *)
    wp_bind (_ <- _)%E.
      iInv "Inv" as (γq' γpop' γm' l1 Pop1 arr1 t1 b1)
        ">(%Enc' & %Bound1 & Phys & Abst & Mono)".
        encode_agree Enc.
      iDestruct "Abst" as "[● P]".
        iDestruct (ghost_var_agree with "γOwn P") as "%". subst Pop1.
        iMod (ghost_var_update_2 true with "γOwn P") as "[γOwn P]"...
      iCombine "● P" as "Abst".
      iDestruct "Phys" as "(A↦ & arr↦ & t↦ & b↦)".
        iDestruct (mapsto_agree with "A↦ AOwn") as "%HA".
          injection HA as [= -> Hsz].
        iDestruct (mapsto_agree with "b↦ bOwn") as "%Hb".
          injection Hb as [=Hb]. apply Nat2Z.inj in Hb. subst b1.
        iCombine "b↦ bOwn" as "b↦". wp_store.
        replace (Z.of_nat b-1)%Z with (Z.of_nat (b-1))...
        iDestruct "b↦" as "[b↦ bOwn]".
        iDestruct (array_agree with "arr↦ arrOwn") as "%"... subst l1.
        clear Hsz.
      iCombine "A↦ arr↦ t↦ b↦" as "Phys".
      iModIntro. iSplitL "Phys Abst Mono".
      { iExists _,_,_, l. fr. }
    wp_pures.

    (* load top *)
    wp_bind (! _)%E.
      iInv "Inv" as (γq' γpop' γm' l2 Pop2 arr2 t2 b2)
        ">(%Enc' & %Bound2 & Phys & Abst & Mono)".
        encode_agree Enc.
      iDestruct "Abst" as "[● P]".
        iDestruct (ghost_var_agree with "γOwn P") as "%". subst Pop2.
      iCombine "● P" as "Abst".
      iDestruct "Phys" as "(A↦ & arr↦ & t↦ & b↦)".
        iDestruct (mapsto_agree with "A↦ AOwn") as "%HA".
          injection HA as [= -> Hsz].
        iDestruct (mapsto_agree with "b↦ bOwn") as "%Hb".
          injection Hb as [=Hb]. apply Nat2Z.inj in Hb.
          assert (b = b2)... subst b2. clear Hb.
        iDestruct (array_agree with "arr↦ arrOwn") as "%"... subst l2.
        clear Hsz.
      iCombine "A↦ arr↦ t↦ b↦" as "Phys".
    
    (* if t < b-1, this load is the commit point *)
    destruct (decide (t2 < b-1)).
    { iMod "AU" as (l') "[Cont [_ Commit]]".
        iDestruct "Cont" as (γq' γpop' γm') "[%Enc' ◯]".
        encode_agree Enc.
      destruct (mod_get_is_Some l (b-1)) as [v Hv]...
      erewrite circ_slice_shrink_right...
      iDestruct "Phys" as "(A↦ & arr↦ & t↦ & b↦)". wp_load.
      iCombine "A↦ arr↦ t↦ b↦" as "Phys".
      iDestruct "Abst" as "[● P]".
        iDestruct (own_ea_agree with "● ◯") as "%". subst l'.
        iMod (own_ea_update (circ_slice l t2 (b-1)) with "● ◯") as "[● ◯]".
        iMod (ghost_var_update_2 false with "γOwn P") as "[γOwn P]"...
      iCombine "● P" as "Abst".
      iDestruct "Mono" as (hl1) "[Mono %HistPref1]".
        iDestruct (mono_deque_pop _ (b-1) with "Mono") as "Mono"...
      iMod ("Commit" $! (circ_slice l t2 (b-1)) (SOMEV v)
        with "[◯]") as "Φ". 1: fr.
      iModIntro. iModIntro.
      
      iSplitL "Phys Abst Mono".
      { iExists _,_,_, l. fr. fr.
        iPureIntro; intros. apply HistPref1... }
      wp_pures. case_bool_decide... wp_pures.

      (* read [b2-1] *)
      wp_bind (! _)%E. rewrite rem_mod_eq...
      iApply (wp_load_offset with "arrOwn")...
      iNext. iIntros "arrOwn".
      wp_pures. case_bool_decide... wp_pures. iApply "Φ". fr.
    }

    (* otherwise... *)
    iDestruct "Phys" as "(A↦ & arr↦ & t↦ & b↦)". wp_load.
    iCombine "A↦ arr↦ t↦ b↦" as "Phys".
    iModIntro. iSplitL "Phys Abst Mono".
    { iExists _,_,_, l. fr. }
    wp_pures.

    (* empty *)
    case_bool_decide as Hbt; wp_pures.
    { wp_bind (_ <- _)%E.
      iInv "Inv" as (γq' γpop' γm' l3 Pop3 arr3 t3 b3)
        ">(%Enc' & %Bound3 & Phys & Abst & Mono)".
        encode_agree Enc.
      iDestruct "Abst" as "[● P]".
        iDestruct (ghost_var_agree with "γOwn P") as "%". subst Pop3.
        iMod (ghost_var_update_2 false with "γOwn P") as "[γOwn P]"...
      iCombine "● P" as "Abst".
      iDestruct "Phys" as "(A↦ & arr↦ & t↦ & b↦)".
        iDestruct (mapsto_agree with "A↦ AOwn") as "%HA".
          injection HA as [= -> Hsz].
        iDestruct (mapsto_agree with "b↦ bOwn") as "%Hb".
          injection Hb as [=Hb]. assert (b = b3)... subst b3. clear Hb.
        replace t2 with b...
        iCombine "bOwn b↦" as "b↦". wp_store.
        iDestruct "b↦" as "[bOwn b↦]".
        iDestruct (array_agree with "arr↦ arrOwn") as "%"... subst l3.
        clear Hsz.
      iCombine "A↦ arr↦ t↦ b↦" as "Phys".
      (* AU *)
      iMod "AU" as (l') "[Cont [_ Commit]]".
      iMod ("Commit" $! l' NONEV with "[Cont]") as "Φ"...
      iModIntro. iSplitL "Phys Abst Mono".
      { iExists _,_,_, l. fr. }
      wp_pures. iApply "Φ". iExists _,_,_, l. fr.
    }
    
    (* read [b2-1] *)
    wp_bind (! _)%E. rewrite rem_mod_eq...
    destruct (mod_get_is_Some l (b-1)) as [v Hv]...
    iApply (wp_load_offset with "arrOwn")...
    iNext. iIntros "arrOwn". wp_pures.

    (* cas top, we already handled normal pop *)
    case_bool_decide... wp_pures.
    wp_bind (CmpXchg _ _ _)%E.
      iInv "Inv" as (γq' γpop' γm' l3 Pop3 arr3 t3 b3)
        ">(%Enc' & %Bound3 & Phys & Abst & Mono)".
        encode_agree Enc.
      iDestruct "Abst" as "[● P]".
        iDestruct (ghost_var_agree with "γOwn P") as "%". subst Pop3.
      iCombine "● P" as "Abst".
      iDestruct "Phys" as "(A↦ & arr↦ & t↦ & b↦)".
        iDestruct (mapsto_agree with "A↦ AOwn") as "%HA".
          injection HA as [= -> Hsz].
        iDestruct (mapsto_agree with "b↦ bOwn") as "%Hb".
          injection Hb as [=Hb]. assert (b = b3)... subst b3. clear Hb.
        iDestruct (array_agree with "arr↦ arrOwn") as "%"... subst l3.
        clear Hsz.
      iCombine "A↦ arr↦ t↦ b↦" as "Phys".
    assert (t2 = b-1)... subst t2. clear n Hbt.
    replace (Z.of_nat (b-1) + 1)%Z with (Z.of_nat b)...
    destruct (decide (b-1 = t3)).
    - (* success *)
      subst t3.
      iDestruct "Phys" as "(A↦ & arr↦ & t↦ & b↦)". wp_cmpxchg_suc.
      iCombine "A↦ arr↦ t↦ b↦" as "Phys".

      (* AU *)
      iMod "AU" as (l') "[Cont [_ Commit]]".
        iDestruct "Cont" as (γq' γpop' γm') "[%Enc' ◯]".
        encode_agree Enc.
      iDestruct "Abst" as "[● P]".
        iDestruct (own_ea_agree with "● ◯") as "%". subst l'.
        erewrite circ_slice_shrink_left... rewrite circ_slice_to_nil...
        iMod (own_ea_update [] with "● ◯") as "[● ◯]".
      iCombine "● P" as "Abst".
      iMod ("Commit" $! [] (SOMEV v) with "[◯]") as "Φ". 1: fr.
      iDestruct "Mono" as (hl1) "[Mono %HistPref1]".
        iMod (mono_deque_pop_singleton _ _ (b-1) with "[Mono]") as "Mono".
        { replace (S (b-1)) with b... }
      replace (S (b-1)) with b...
      iModIntro. iSplitL "Phys Abst Mono".
        { iExists _,_,_, l,true,_,b,b. fr.
          rewrite circ_slice_to_nil... iFrame. fr... }
      wp_pures.

      (* store bot *)
      replace (Z.of_nat (b-1) + 1)%Z with (Z.of_nat b)...
      wp_bind (_ <- _)%E.

      iInv "Inv" as (γq' γpop' γm' l4 Pop4 arr4 t4 b4)
        ">(%Enc' & %Bound4 & Phys & Abst & Mono)".
        encode_agree Enc.
      iDestruct "Abst" as "[● P]".
        iDestruct (ghost_var_agree with "γOwn P") as "%". subst Pop4.
        iMod (ghost_var_update_2 false with "γOwn P") as "[γOwn P]"...
      iCombine "● P" as "Abst".
      iDestruct "Phys" as "(A↦ & arr↦ & t↦ & b↦)".
        iDestruct (mapsto_agree with "A↦ AOwn") as "%HA".
          injection HA as [= -> Hsz].
        iDestruct (mapsto_agree with "b↦ bOwn") as "%Hb".
          injection Hb as [=Hb]. assert (b = b4)... subst b4. clear Hb.
        iDestruct (array_agree with "arr↦ arrOwn") as "%"... subst l4.
        clear Hsz.
        iCombine "bOwn b↦" as "b↦". wp_store.
        iDestruct "b↦" as "[bOwn b↦]".
      iCombine "A↦ arr↦ t↦ b↦" as "Phys".
      iModIntro. iSplitL "Phys Abst Mono".
      { iExists _,_,_, l. fr. }
      wp_pures. iApply "Φ". iExists _,_,_, l. fr.
    - (* fail *)
      iDestruct "Phys" as "(A↦ & arr↦ & t↦ & b↦)".
        wp_cmpxchg_fail. { intro NO. injection NO... }
      iCombine "A↦ arr↦ t↦ b↦" as "Phys".

      iMod "AU" as (l') "[Cont [_ Commit]]".
      iMod ("Commit" $! l' NONEV with "[Cont]") as "Φ"...
      iModIntro. iSplitL "Phys Abst Mono".
        { iExists _,_,_, l. fr. }
      wp_pures.

      (* store bot *)
      replace (Z.of_nat (b-1) + 1)%Z with (Z.of_nat b)...
      wp_bind (_ <- _)%E.
      iInv "Inv" as (γq' γpop' γm' l4 Pop4 arr4 t4 b4)
        ">(%Enc' & %Bound4 & Phys & Abst & Mono)".
        encode_agree Enc.
      iDestruct "Abst" as "[● P]".
        iDestruct (ghost_var_agree with "γOwn P") as "%". subst Pop4.
        iMod (ghost_var_update_2 false with "γOwn P") as "[γOwn P]"...
      iCombine "● P" as "Abst".
      iDestruct "Phys" as "(A↦ & arr↦ & t↦ & b↦)".
        iDestruct (mapsto_agree with "A↦ AOwn") as "%HA".
          injection HA as [= -> Hsz].
        iDestruct (mapsto_agree with "b↦ bOwn") as "%Hb".
          injection Hb as [=Hb]. assert (b = b4) by lia. subst b4. clear Hb.
          iCombine "bOwn b↦" as "b↦". wp_store.
          iDestruct "b↦" as "[bOwn b↦]".
        iDestruct (array_agree with "arr↦ arrOwn") as "%"... subst l4.
        clear Hsz.
      iCombine "A↦ arr↦ t↦ b↦" as "Phys".

      iModIntro. iSplitL "Phys Abst Mono".
      { iExists _,_,_, l. fr. }
      wp_pures. iApply "Φ". iExists _,_,_, l. fr.
  Qed.
*)
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
    iIntros "#Inv" (Φ) "AU".
      iDestruct "Inv" as (γq γpop γm A top bot) "(%Q & %Enc & Inv)".
      rewrite Q.
    wp_lam. unfold code.arr, code.top, code.bot. wp_pures.

    (* load top *)
    wp_bind (! _)%E.
    iInv "Inv" as (l1 t1 b1) "(>%Htb1 & Circle & >top↦ & Bot & Log)".
      wp_load.
    iModIntro. iSplitL "Circle top↦ Bot Log"; fr.
    wp_pures.

    (* load bot *)
    wp_bind (! _)%E.
    iInv "Inv" as (l2 t2 b2) "(>%Htb2 & Circle & top↦ & >Bot & Log)".
      iDestruct "Bot" as (Pop2) "[bot↦ Pop]". wp_load.
      iCombine "bot↦ Pop" as "Bot".
    iModIntro. iSplitL "Circle top↦ Bot Log"; fr.
    wp_pures.

    (* load array *)
    wp_alloc arr as "arr↦". wp_pures.
    wp_bind (! _)%E.
    iInv "Inv" as (l3 t3 b3) "(>%Htb3 & Circle & top↦ & Bot & Log)".
      iDestruct "Circle" as (γC3 ca3) "(A↦ & #🌀3 & 🎯 & 📚)". wp_load.
      iCombine "A↦ 🌀3 🎯 📚" as "Circle".
    iModIntro. iSplitL "Circle top↦ Bot Log"; fr.
    wp_store.

    replace (
      if Pop2 then LitInt (Z.of_nat b2 - 1) else LitInt (Z.of_nat b2)
    ) with (
      LitInt (Z.of_nat (if Pop2 then b2 - 1 else b2))
    ); last first.
    { destruct Pop2... admit. }
    wp_pures.

    (* no chance to steal *)
    case_bool_decide as Hif; wp_pures.
    { iMod "AU" as (l) "[Cont [_ Commit]]".
      iMod ("Commit" $! l NONEV with "[Cont]") as "Φ"...
      iApply "Φ"... }
    (*assert (t1 < b2) as Htb12. 1: destruct Pop2...*)

    (* get_circle *)
    wp_load. wp_bind (get_circle _ _)%E.
    awp_apply get_circle_spec...
    iInv "Inv" as (l4 t4 b4) "(>%Htb4 & Circle & top↦ & Bot & Log)".
      iDestruct "Circle" as (γC4 ca4) "(A↦ & #🌀4 & 🎯 & 📚)".
      destruct (decide (γC3 = γC4)).
      - subst γC4.
        unfold circle_content. iDestruct "🎯" as ">🎯".
        iAaccIntro with "[🎯]".
  Admitted.
End proof.

Program Definition atomic_deque `{!heapGS Σ, !dequeG Σ} :
  spec.atomic_deque Σ :=
  {| spec.new_deque_spec := new_deque_spec;
     spec.push_spec := push_spec;
     spec.pop_spec := pop_spec;
     spec.steal_spec := steal_spec;
     spec.deque_content_exclusive := deque_content_exclusive |}.

Global Typeclasses Opaque deque_content is_deque.

