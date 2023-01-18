From iris.algebra Require Import list excl_auth mono_nat.
From iris.bi Require Import derived_laws_later.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import invariants ghost_var ghost_map.
From chase_lev Require Import mono_nat atomic.
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

  Definition push : val :=
    λ: "deque" "v",
      let: "b" := !(bot "deque") in
      let: "t" := !(top "deque") in
      let: "array" := !(arr "deque") in
      let: "sz" := size_circle "array" in
      (if: "t" + "sz" ≤ "b" + #1
        then arr "deque" <- grow_circle "array" "t" "b"
        else #()
      ) ;;
      set_circle !(arr "deque") "b" "v" ;;
      bot "deque" <- "b" + #1.
  
  Definition pop : val :=
    λ: "deque",
      let: "b" := !(bot "deque") - #1 in
      let: "array" := !(arr "deque") in
      bot "deque" <- "b" ;;
      let: "t" := !(top "deque") in
      if: "b" < "t" then (* empty pop *)
        bot "deque" <- "t" ;; NONE
      else let: "v" := get_circle "array" "b" in
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
    mono_natG :> mono_natG Σ;
    geltsG :> ghost_mapG Σ nat val;
    archiveG :> inG Σ mono_natR;
    eraG :> ghost_varG Σ (nat * gname * list val)
  }.

Definition dequeΣ : gFunctors :=
  #[GFunctor (excl_authR $ listO valO);
    ghost_varΣ bool;
    mono_natΣ;
    ghost_mapΣ nat val;
    GFunctor mono_natR;
    ghost_varΣ (nat * gname * list val)
  ].

Global Instance subG_dequeΣ {Σ} : subG dequeΣ Σ → dequeG Σ.
Proof. solve_inG. Qed.

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
  repeat iIntros; repeat iSplit; extended_auto;
  repeat iIntros; repeat iExists _;
  try iFrame "arr↦"; try iFrame "arr↦1"; try iFrame "arr↦2"; 
  iFrame; eauto.

Section some.
  Context `{!heapGS Σ, !dequeG Σ}.
  Notation iProp := (iProp Σ).
  Definition glob_gnames := gname.

  Definition top_bot_state (t b : nat) : nat :=
    2*t + (if bool_decide (t < b) then 1 else 0).

  Definition some_frag (γglob : glob_gnames) (era : nat)
  (γcont : gname) (ca : val) (l : list val) (t b : nat) : iProp.
    Admitted.

  Definition some_archived (γglob : glob_gnames) (era : nat)
  (γcont : gname) (ca : val) (l : list val) (t b : nat) : iProp.
    Admitted.

  Definition some_auth (γglob : glob_gnames) (era : nat)
  (γcont : gname) (ca : val) (l : list val) (t b : nat) : iProp.
    Admitted.

  (* Timeless & Persistent *)
  (*
  Ltac desγ H1 H2 :=
    destruct H1 as (((γall,γarch),γelt),γt); destruct H2 as (γcont,era).
  *)

  Global Instance some_frag_timeless γglob era γcont ca l t b :
    Timeless (some_frag γglob era γcont ca l t b).
  Admitted.

  Global Instance some_frag_persistent γglob era γcont ca l t b :
    Persistent (some_frag γglob era γcont ca l t b).
  Admitted.
  
  Global Instance some_archived_timeless γglob era γcont ca l t b :
    Timeless (some_archived γglob era γcont ca l t b).
  Admitted.

  Global Instance some_archived_persistent γglob era γcont ca l t b :
    Persistent (some_archived γglob era γcont ca l t b).
  Admitted.

  Global Instance some_auth_timeless γglob era γcont ca l t b :
    Timeless (some_auth γglob era γcont ca l t b).
  Admitted.
  
  Lemma top_bot_state_le t1 b1 t2 b2 :
    top_bot_state t1 b1 ≤ top_bot_state t2 b2 ↔
    t1 ≤ t2 ∧ (t1 = t2 ∧ t1 < b1 → t2 < b2).
  Proof. unfold top_bot_state. do 2 case_bool_decide; lia. Qed.

  Lemma some_auth_alloc γcont ca l t :
    length l ≠ 0 →
    ⊢ |==> ∃ (γglob : glob_gnames),
      some_auth γglob 0 γcont ca l t t.
  Admitted.

  Lemma some_frag_agree γglob era γcont1 ca1 l1 t1 b1
  γcont2 ca2 l2 t2 b2 :
    some_frag γglob era γcont1 ca1 l1 t1 b1 -∗
    some_frag γglob era γcont2 ca2 l2 t2 b2 -∗
    ⌜γcont1 = γcont2 ∧ ca1 = ca2⌝.
  Admitted.

  Lemma some_get_frag γglob era γcont ca l t b :
    some_auth γglob era γcont ca l t b -∗
    some_frag γglob era γcont ca l t b.
  Admitted.

  Lemma some_get_archived γglob era1 γcont1 ca1 l1 t1 b1
  era2 γcont2 ca2 l2 t2 b2 :
    (* era1 is later than era2 *)
    era1 ≠ era2 →
    some_auth γglob era1 γcont1 ca1 l1 t1 b1 -∗
    some_frag γglob era2 γcont2 ca2 l2 t2 b2 -∗
    ∃ l' t' b', some_archived γglob era2 γcont2 ca2 l' t' b'.
  Admitted.

  Lemma some_get_lb γglob era1 γcont1 ca1 l1 t1 b1
  γcont2 era2 ca2 l2 t2 b2 :
    (* era1 is later than era2 *)
    some_auth γglob era1 γcont1 ca1 l1 t1 b1 -∗
    some_frag γglob era2 γcont2 ca2 l2 t2 b2 -∗
    ⌜t2 ≤ t1 ∧ (
      (t2 = t1 ∧ t2 < b2) →
      (t1 < b1 ∧ mod_get l2 t2 = mod_get l1 t1)
    )⌝.
  Admitted.

  Lemma some_archived_get_frag γglob era γcont ca l t b :
    some_archived γglob era γcont ca l t b -∗
    some_frag γglob era γcont ca l t b.
  Admitted.

  Lemma some_archived_get_lb γglob era γcont ca l1 t1 b1 l2 t2 b2 :
    some_archived γglob era γcont ca l1 t1 b1 -∗
    some_frag γglob era γcont ca l2 t2 b2 -∗
    ⌜t2 ≤ t1 ∧ (
      (t2 = t1 ∧ t2 < b2) →
      (t1 < b1 ∧ mod_get l2 t2 = mod_get l1 t1)
    )⌝.
  Admitted.

  Lemma some_archived_get_circle γglob era γcont ca l t b :
    some_archived γglob era γcont ca l t b -∗
    persistent_circle ca l.
  Admitted.

  Lemma some_auth_write_bot v γglob era γcont ca l t b :
    some_auth γglob era γcont ca l t b -∗
    some_auth γglob era γcont ca (mod_set l b v) t b.
  Admitted.

  Lemma some_auth_update γglob era γcont ca l t b :
    t < b →
    some_auth γglob era γcont ca l t b ==∗
    some_auth γglob era γcont ca l (S t) b.
  Admitted.

  Lemma some_auth_update_bot γglob era γcont ca l t b :
    S b < t + length l →
    some_auth γglob era γcont ca l t b ==∗
    some_auth γglob era γcont ca l t (S b).
  Admitted.

  Lemma some_auth_archive γcont' ca' l' γglob era γcont ca l t b :
    length l ≤ length l' →
    own_circle ca l -∗
    some_auth γglob era γcont ca l t b ==∗
    some_archived γglob era γcont ca l t b ∗
    some_auth γglob (S era) γcont' ca' l' t b.
  Admitted.
End some.

Section proof.
  Context `{!heapGS Σ, !dequeG Σ, !circleG Σ} (N : namespace).
  Notation iProp := (iProp Σ).

  Let circleN := N .@ "circle".
  Let dequeN := N .@ "deque".

  Definition deque_inv (γq γpop γera : gname) (γglob : glob_gnames)
  (A top bot : loc) : iProp :=
    ∃ (γcont : gname) (era : nat) (ca : val) (l : list val) (t b : nat),
      ⌜1 ≤ t ≤ b ∧ b < t + length l ∧ length l ≠ 0⌝ ∗
      (* abstract states *)
      ( some_auth γglob era γcont ca l t b ∗
        own γq (●E (circ_slice l t b)) ∗
        ghost_var γera (1/2) (era, γcont, l)
      ) ∗
      (* circular array *)
      ( A ↦{#1/2} ca ∗ 
        is_circle circleN γcont ca ∗ circle_content γcont l
      ) ∗
      (* top *)
      top ↦ #t ∗
      (* bottom *)
      ( ∃ (Popping : bool),
        let bp := if Popping then b-1 else b in
        bot ↦{#1/2} #bp ∗
        ghost_var γpop (1/2) Popping
      ).

  Definition is_deque (γ : gname) (q : val) : iProp :=
    ∃ (γq γpop γera : gname) (γglob : glob_gnames) (A top bot : loc),
      ⌜q = (#A, #top, #bot)%V⌝ ∗
      ⌜γ = encode (γq, γpop, γera, γglob)⌝ ∗
      inv dequeN (deque_inv γq γpop γera γglob A top bot).
  Global Instance is_deque_persistent γ q :
    Persistent (is_deque γ q) := _.

  Definition deque_content (γ : gname) (frag : list val) : iProp :=
    ∃ (γq γpop γera : gname) (γglob : glob_gnames),
      ⌜γ = encode (γq, γpop, γera, γglob)⌝ ∗
      own γq (◯E frag).
  Global Instance deque_content_timeless γ frag :
    Timeless (deque_content γ frag) := _.

  (* owner of the deque who can call push and pop *)
  Definition own_deque (γ : gname) (q : val) : iProp :=
    ∃ (γq γpop γera : gname) (γglob : glob_gnames)
    (γcont : gname) (era : nat)
    (ca : val) (l : list val) (A top bot : loc) (b : nat),
      ⌜γ = encode (γq, γpop, γera, γglob)⌝ ∗
      ⌜q = (#A, #top, #bot)%V⌝ ∗
      (* array state *)
      ghost_var γera (1/2) (era, γcont, l) ∗
      (* own circle *)
      A ↦{#1/2} ca ∗ own_circle ca l ∗
      (* own bottom *)
      bot ↦{#1/2} #b ∗ ghost_var γpop (1/2) false.
  
  Lemma deque_content_exclusive γ frag1 frag2 :
    deque_content γ frag1 -∗ deque_content γ frag2 -∗ False.
  Proof.
    iIntros "C1 C2".
      iDestruct "C1" as (γq γpop γera γglob) "[%Enc C1]".
      iDestruct "C2" as (γq' γpop' γera' γglob') "[%Enc' C2]".
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
    wp_bind (new_circle _)%E.
    iApply (new_circle_spec circleN)...
    iIntros (γcont ca l) "!> (%Len & IC & IsC & Ⓜ️)". wp_pures.
    wp_alloc bot as "[b↦1 b↦2]". wp_alloc top as "t↦".
    wp_alloc A as "[A↦1 A↦2]". wp_pures.

    (* make resources *)
    iMod (own_alloc (●E [] ⋅ ◯E [])) as (γq) "[γq● γq◯]".
      1: apply excl_auth_valid.
    iMod (ghost_var_alloc false) as (γpop) "[γpop1 γpop2]".
    iMod (some_auth_alloc γcont ca l 1) as (γglob) "Auth"...
    iMod (ghost_var_alloc (0, γcont, l)) as (γera) "[eraG1 eraG2]".
    iMod (inv_alloc dequeN _ (deque_inv γq γpop γera γglob A top bot)
      with "[A↦1 t↦ b↦1 IC IsC γq● γpop1 Auth eraG1]") as "Inv".
    { fr. fr. }

    (* apply Φ *)
    iApply "HΦ". iModIntro. iSplitL "Inv"; first fr.
    iSplitL "γq◯"; first fr. iExists _,_,_,_,_,_,_,l. fr. fr.
    instantiate (1:=1)...
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
      iDestruct "Own" as (γq γpop γera γglob γcont) "Own".
        iDestruct "Own" as (era ca l A top bot b) "Own".
        iDestruct "Own" as "(%Enc & %Q & eraOwn & AOwn & caOwn & bOwn & popOwn)".
        subst q.
      iDestruct "Is" as (γq' γpop' γera' γglob') "Inv".
        iDestruct "Inv" as (A' top' bot') "Inv".
        iDestruct "Inv" as "(%Q & %Enc' & Inv)".
        injection Q as [= <- <- <-]. encode_agree Enc.
    wp_lam. unfold code.arr, code.top, code.bot. wp_pures.
    wp_load. wp_pures.

    (* 1. load top *)
    wp_bind (! _)%E.
      iInv "Inv" as (γcont1 era1 ca1 l1 t1 b1) "Invs".
        iDestruct "Invs" as "(>%Htb1 & >Abst & A & >Top & >Bot)".
      iDestruct "Abst" as "(Glob & Q & Era)".
        iDestruct (some_get_frag with "Glob") as "#F1".
        iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq".
        injection Eq as [= <- <- <-].
      iCombine "Glob Q Era" as "Abst".
      iDestruct "A" as "(>A↦ & #IsC1 & ContC)".
        iDestruct (mapsto_agree with "AOwn A↦") as "%". subst ca1.
      iCombine "A↦ IsC1 ContC" as "A".
      iDestruct "Bot" as (Pop1) "[bot↦ pop]".
        iDestruct (ghost_var_agree with "pop popOwn") as "%". subst Pop1.
        iDestruct (mapsto_agree with "bot↦ bOwn") as "%Eq".
        injection Eq as [= Eq]. assert (b = b1)... subst b1. clear Eq.
      iCombine "bot↦ pop" as "Bot".
      wp_load.
      iModIntro. iSplitL "Abst A Top Bot"; fr.
      { fr. instantiate (1:=false)... }
    wp_pures. wp_load. wp_pures.

    (* 2. get size *)
    awp_apply size_circle_spec...
      iInv "Inv" as (γcont' era2 ca2 l2 t2 b2) "Invs".
        iDestruct "Invs" as "(>%Htb2 & >Abst & A & >Top & >Bot)".
      iDestruct "Abst" as "(Glob & Q & Era)".
        iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq".
        injection Eq as [= <- <- <-].
      iCombine "Glob Q Era" as "Abst".
      iDestruct "A" as "(>A↦ & #IsC2 & >ContC)".
        iDestruct (mapsto_agree with "AOwn A↦") as "%". subst ca2.
        iAaccIntro with "ContC".
      all: iIntros "ContC"; iCombine "A↦ IsC1 ContC" as "A".
      all: iSplitL "Abst A Top Bot"; fr.
    iIntros "!> _". wp_pures.
    
    case_bool_decide; last first; wp_pures.
    - (* no growing *)
      wp_load.
      (* 3. write to circle *)
      awp_apply (set_circle_spec with "[] caOwn")...
        iInv "Inv" as (γcont3 era3 ca3 l3 t3 b3) "Invs".
          iDestruct "Invs" as "(>%Htb3 & >Abst & A & >Top & >Bot)".
        iDestruct "Abst" as "(Glob & Q & Era)".
          iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq".
          injection Eq as [= <- <- <-].
        iCombine "Glob Q Era" as "Abst".
        iDestruct "Bot" as (Pop3) "[bot↦ pop]".
          iDestruct (ghost_var_agree with "pop popOwn") as "%Eq". subst Pop3.
          iDestruct (mapsto_agree with "bOwn bot↦") as "%Eq".
            injection Eq as [= Hb3]. assert (b = b3)... subst b3. clear Hb3.
        iCombine "bot↦ pop" as "Bot".
        iDestruct "A" as "(>A↦ & #IsC3 & >ContC)".
          iDestruct (mapsto_agree with "AOwn A↦") as "%". subst ca3.
          iAaccIntro with "ContC".
        all: iIntros "ContC"; iCombine "A↦ IsC3 ContC" as "A".
        { iSplitL "Abst A Top Bot"; fr. iModIntro; iNext.
          fr. iExists false. fr. }
      
      iDestruct "Abst" as "(Glob & Q & Era)".
        iDestruct (some_auth_write_bot v with "Glob") as "Glob".
        iMod (ghost_var_update_2 (era, γcont, mod_set l b v)
          with "eraOwn Era"
        ) as "[eraOwn Era]"...
      iCombine "Glob Q Era" as "Abst".

      unfold deque_inv.
      iSplitL "Abst A Top Bot".
      { iExists γcont, era, ca, (mod_set l b v), t3, b.
        iModIntro; iNext. fr.
        all: try rewrite insert_length...
        rewrite circ_slice_update_right...
        fr. iExists false. fr. }
      iIntros "!> caOwn". wp_pures.

      (* 4. increment bot *)
      iInv "Inv" as (γcont4 era4 ca4 l4 t4 b4) "Invs".
        iDestruct "Invs" as "(>%Htb4 & >Abst & A & >Top & >Bot)".
        iDestruct "Bot" as (Pop4) "[bot↦ pop]".
          iDestruct (ghost_var_agree with "pop popOwn") as "%Eq". subst Pop4.
          iDestruct (mapsto_agree with "bOwn bot↦") as "%Eq".
            injection Eq as [= Hb4]. assert (b = b4)... subst b4. clear Hb4.
          iCombine "bOwn bot↦" as "bot↦".
            wp_store. replace (Z.of_nat b + 1)%Z with (Z.of_nat (S b))...
          iDestruct "bot↦" as "[bOwn bot↦]".
        iCombine "bot↦ pop" as "Bot".
        iDestruct "Abst" as "(Glob & Q & Era)".
          iDestruct (some_get_lb with "Glob F1") as "%Ht14".
          iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq".
          injection Eq as [= <- <- <-].
        iCombine "Glob Q Era" as "Abst".
        iDestruct "A" as "(A↦ & #IsC4 & ContC)".
          iDestruct (mapsto_agree with "AOwn A↦") as "%". subst ca4.
        iCombine "A↦ IsC4 ContC" as "A".
      iMod "AU" as (l') "[Cont [_ Commit]]".
        iDestruct "Cont" as (γq' γpop' γera' γbglob') "[%Enc' ◯]".
          encode_agree Enc.
        iDestruct "Abst" as "(Glob & Q & Era)".
          iMod (some_auth_update_bot with "Glob") as "Glob".
            1: rewrite insert_length...
          iDestruct (own_ea_agree with "Q ◯") as "%Hl'".
          iMod (own_ea_update (l' ++ [v]) with "Q ◯") as "[Q ◯]".
        iCombine "Glob Q Era" as "Abst".
      iMod ("Commit" with "[◯]") as "HΦ". 1: fr.
      
      iModIntro.
      iSplitL "A Abst Top Bot".
      { iExists γcont, era, ca, (mod_set l b v), t4, (S b). fr.
        - rewrite mod_set_length...
        - rewrite (circ_slice_extend_right _ _ _ v)...
          2: rewrite mod_set_get... subst l'. fr.
          iExists false...
      }
      iApply "HΦ".
        iExists γq, γpop, γera, γglob, γcont.
        iExists era, ca, (mod_set l b v), A, top, bot, (S b).
        fr.
    - (* X. grow *)
      wp_bind (grow_circle _ _ _)%E.
      awp_apply (grow_circle_spec _ _ _ l with "[] [caOwn]")...
        iInv "Inv" as (γcontX eraX caX lX tX bX) "Invs".
          iDestruct "Invs" as "(>%HtbX & >Abst & A & >Top & >Bot)".
        iDestruct "Abst" as "(Glob & Q & Era)".
          iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq".
          injection Eq as [= <- <- <-].
        iCombine "Glob Q Era" as "Abst".
        iDestruct "A" as "(>A↦ & #IsCXpre & >ContC)".
          iDestruct (mapsto_agree with "AOwn A↦") as "%". subst caX.
          iAaccIntro with "ContC".
        { iIntros "ContC"; iCombine "A↦ IsCXpre ContC" as "A".
          iSplitL "Abst A Top Bot"; fr. }
      iIntros (γcontX caX lX) "(%HlenX & %Heqs & #IsCX & Cont & ContX)".
        iCombine "A↦ IsCXpre Cont" as "A".
        iSplitL "A Abst Top Bot"; fr.
      iIntros "!> [Own OwnX]". wp_pures.

      (* Y. replace array *)
      wp_bind (_ <- _)%E.
        iInv "Inv" as (γcontY eraY caY lY tY bY) "Invs".
          iDestruct "Invs" as "(>%HtbY & >Abst & A & >Top & >Bot)".
        iDestruct "A" as "(>A↦ & #IsCY & >ContC)".
          iDestruct (mapsto_agree with "AOwn A↦") as "%". subst caY.
          iCombine "AOwn A↦" as "A↦". wp_store.
          iDestruct "A↦" as "[AOwn A↦]".
        iCombine "A↦ IsCX ContX" as "A".
        iDestruct "Bot" as (Pop3) "[bot↦ pop]".
          iDestruct (ghost_var_agree with "pop popOwn") as "%Eq". subst Pop3.
          iDestruct (mapsto_agree with "bOwn bot↦") as "%Eq".
            injection Eq as [= HbY]. assert (b = bY)... subst bY. clear HbY.
        iCombine "bot↦ pop" as "Bot".
        iDestruct "Abst" as "(Glob & Q & Era)".
          iDestruct (some_get_lb with "Glob F1") as "%Ht1Y".
          iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq".
          injection Eq as [= <- <- <-].
          iMod (some_auth_archive γcontX caX lX with "Own Glob") as "[#Arch Glob]"...
          iMod (ghost_var_update_2 (S era, γcontX, lX)
            with "eraOwn Era") as "[eraOwn Era]"...
        iCombine "Glob Q Era" as "Abst".
      replace (circ_slice l tY b) with (circ_slice lX tY b); last first.
      { rewrite (circ_slice_split l t1 tY b) in Heqs...
        rewrite (circ_slice_split lX t1 tY b) in Heqs...
        apply app_inj_1 in Heqs as [_ Heqs]...
        rewrite circ_slice_length... rewrite circ_slice_length... }
      iSplitL "A Abst Top Bot".
      { iModIntro; iNext. unfold deque_inv.
        iExists γcontX, (S era), caX, lX, tY, b.
        fr. fr. instantiate (1:=false)... }
      iModIntro. wp_pures. wp_load. wp_pures.

      (* 3. write to circle *)
      iRename "OwnX" into "caOwn".
      iRename "ContC" into "ContCpast".
      awp_apply (set_circle_spec with "[] caOwn")...
        iInv "Inv" as (γcont3 era3 ca3 l3 t3 b3) "Invs".
          iDestruct "Invs" as "(>%Htb3 & >Abst & A & >Top & >Bot)".
        iDestruct "Abst" as "(Glob & Q & Era)".
          iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq".
          injection Eq as [= <- <- <-].
        iCombine "Glob Q Era" as "Abst".
        iDestruct "Bot" as (Pop3) "[bot↦ pop]".
          iDestruct (ghost_var_agree with "pop popOwn") as "%Eq". subst Pop3.
          iDestruct (mapsto_agree with "bOwn bot↦") as "%Eq".
            injection Eq as [= Hb3]. assert (b = b3)... subst b3. clear Hb3.
        iCombine "bot↦ pop" as "Bot".
        iDestruct "A" as "(>A↦ & #IsC3 & >ContC)".
          iDestruct (mapsto_agree with "AOwn A↦") as "%". subst ca3.
          iAaccIntro with "ContC".
        all: iIntros "ContC"; iCombine "A↦ IsC3 ContC" as "A".
        { iSplitL "Abst A Top Bot"; fr. iModIntro; iNext.
          fr. iExists false. fr. }
      
      iDestruct "Abst" as "(Glob & Q & Era)".
        iDestruct (some_auth_write_bot v with "Glob") as "Glob".
        iMod (ghost_var_update_2 (S era, γcontX, mod_set lX b v)
          with "eraOwn Era"
        ) as "[eraOwn Era]"...
      iCombine "Glob Q Era" as "Abst".

      unfold deque_inv.
      iSplitL "Abst A Top Bot".
      { iExists γcontX, (S era), caX, (mod_set lX b v), t3, b.
        iModIntro; iNext. fr.
        all: try rewrite insert_length...
        rewrite circ_slice_update_right...
        fr. iExists false. fr. }
      iIntros "!> caOwn". wp_pures.

      (* 4. increment bot *)
      iInv "Inv" as (γcont4 era4 ca4 l4 t4 b4) "Invs".
        iDestruct "Invs" as "(>%Htb4 & >Abst & A & >Top & >Bot)".
        iDestruct "Bot" as (Pop4) "[bot↦ pop]".
          iDestruct (ghost_var_agree with "pop popOwn") as "%Eq". subst Pop4.
          iDestruct (mapsto_agree with "bOwn bot↦") as "%Eq".
            injection Eq as [= Hb4]. assert (b = b4)... subst b4. clear Hb4.
          iCombine "bOwn bot↦" as "bot↦".
            wp_store. replace (Z.of_nat b + 1)%Z with (Z.of_nat (S b))...
          iDestruct "bot↦" as "[bOwn bot↦]".
        iCombine "bot↦ pop" as "Bot".
        iDestruct "Abst" as "(Glob & Q & Era)".
          iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq".
          injection Eq as [= <- <- <-].
        iCombine "Glob Q Era" as "Abst".
        iDestruct "A" as "(A↦ & #IsC4 & ContC)".
          iDestruct (mapsto_agree with "AOwn A↦") as "%". subst ca4.
        iCombine "A↦ IsC4 ContC" as "A".
      iMod "AU" as (l') "[Cont [_ Commit]]".
        iDestruct "Cont" as (γq' γpop' γera' γbglob') "[%Enc' ◯]".
          encode_agree Enc.
        iDestruct "Abst" as "(Glob & Q & Era)".
          iDestruct (some_get_lb with "Glob F1") as "%Ht14".
          iMod (some_auth_update_bot with "Glob") as "Glob".
            1: rewrite insert_length...
          iDestruct (own_ea_agree with "Q ◯") as "%Hl'".
          iMod (own_ea_update (l' ++ [v]) with "Q ◯") as "[Q ◯]".
        iCombine "Glob Q Era" as "Abst".
      iMod ("Commit" with "[◯]") as "HΦ". 1: fr.
      
      iModIntro.
      iSplitL "A Abst Top Bot".
      { iExists γcontX, (S era), caX, (mod_set lX b v), t4, (S b). fr.
        - rewrite mod_set_length...
        - rewrite (circ_slice_extend_right _ _ _ v)...
          2: rewrite mod_set_get... subst l'. fr.
          iExists false...
      }
      iApply "HΦ".
        iExists γq, γpop, γera, γglob, γcontX.
        iExists (S era), caX, (mod_set lX b v), A, top, bot, (S b).
        fr.
      Unshelve. done.
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
  Admitted.

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
      iDestruct "Is" as (γq γpop γcont γglob A top bot) "Is".
      iDestruct "Is" as "(%Q & %Enc & Inv)".
      subst q.
    wp_lam. unfold code.arr, code.top, code.bot. wp_pures.

    (* 1. load top *)
    wp_bind (! _)%E.
      iInv "Inv" as (γcont1 era1 ca1 l1 t1 b1) "Invs".
        iDestruct "Invs" as "(>%Htb1 & >Abst & A & >Top & >Bot)".
      iDestruct "Abst" as "(Glob & Q & Era)".
        iDestruct (some_get_frag with "Glob") as "#F1".
      iCombine "Glob Q Era" as "Abst".
      wp_load.
    iModIntro. iSplitL "Abst A Top Bot"; fr.
    wp_pures.

    (* 2. load bot *)
    wp_bind (! _)%E.
      iInv "Inv" as (γcont2 era2 ca2 l2 t2 b2) "Invs".
        iDestruct "Invs" as "(>%Htb2 & >Abst & A & >Top & >Bot)".
      iDestruct "Abst" as "(Glob & Q & Era)".
        iDestruct (some_get_frag with "Glob") as "#F2".
        iDestruct (some_get_lb with "Glob F1") as "%Lb12".
      iCombine "Glob Q Era" as "Abst".
      iDestruct "Bot" as (Pop2) "[bot↦ Pop]". wp_load.
      iCombine "bot↦ Pop" as "Bot".
    iModIntro. iSplitL "Abst A Top Bot"; fr.
    wp_pures.

    (* 3. load array *)
    wp_alloc arr as "arr↦". wp_pures.
    wp_bind (! _)%E.
      iInv "Inv" as (γcont3 era3 ca3 l3 t3 b3) "Invs".
        iDestruct "Invs" as "(>%Htb3 & >Abst & A & >Top & >Bot)".
      iDestruct "Abst" as "(Glob & Q & Era)".
        iDestruct (some_get_frag with "Glob") as "#F3".
        iDestruct (some_get_lb with "Glob F2") as "%Lb23".
      iCombine "Glob Q Era" as "Abst".
      iDestruct "A" as "(>A↦ & #IsC3 & >ContC)". wp_load.
      iCombine "A↦ IsC3 ContC" as "A".
    iModIntro. iSplitL "Abst A Top Bot"; fr.
    wp_store. wp_pures.

    (* no chance to steal *)
    case_bool_decide as Hif; wp_pures.
    { iMod "AU" as (l) "[Cont [_ Commit]]".
      iMod ("Commit" $! l NONEV with "[Cont]") as "Φ"...
      iApply "Φ"... }
    assert (t1 < b2) as Htb12. 1: destruct Pop2...

    (* 4. get_circle *)
    wp_load. wp_bind (get_circle _ _)%E.
    awp_apply get_circle_spec...
      iInv "Inv" as (γcont4 era4 ca4 l4 t4 b4) "Invs".
        iDestruct "Invs" as "(>%Htb4 & >Abst & A & >Top & >Bot)".
      iDestruct "Abst" as "(Glob & Q & Era)".
        iDestruct (some_get_frag with "Glob") as "#F4".
        iDestruct (some_get_lb with "Glob F3") as "%Lb34".
      iCombine "Glob Q Era" as "Abst".
    destruct (decide (era3 = era4)) as [eqγ|neqγ].
    - (* array was not archived *)
      subst era4.
      iDestruct (some_frag_agree with "F3 F4") as "[% %]".
        subst γcont4 ca4.
      iDestruct "A" as "(>A↦ & #IsC4 & >ContC)".
        iAaccIntro with "[ContC]".
        { unfold tele_app.
          instantiate (1:= {| tele_arg_head := l4;
            tele_arg_tail := {| tele_arg_head := true |}
          |})... }
          all: simpl. { instantiate (1:=()). fr. fr. }
          simpl. iIntros (x) "[%Hx ContC]".
      iCombine "A↦ IsC4 ContC" as "A".
      iModIntro. iSplitL "Abst A Top Bot"; fr.
      wp_pures.
      
      (* 5. CAS *)
      wp_bind (CmpXchg _ _ _)%E.
      iInv "Inv" as (γcont5 era5 ca5 l5 t5 b5) "Invs".
        iDestruct "Invs" as "(>%Htb5 & >Abst & A & >Top & >Bot)".
        iDestruct "Abst" as "(Glob & Q & Era)".
          iDestruct (some_get_frag with "Glob") as "#F5".
          iDestruct (some_get_lb with "Glob F4") as "%Lb45".
        iCombine "Glob Q Era" as "Abst".
      destruct (decide (t1 = t5)); last first.
      { (* fail *)
        wp_cmpxchg_fail. { intro NO. inversion NO... }
        iMod "AU" as (lau) "[Cont [_ Commit]]".
        iMod ("Commit" $! lau NONEV with "[Cont]") as "HΦ"...
        iModIntro. iSplitL "Abst A Top Bot"; fr.
        wp_pures. iApply "HΦ"...
      }
      (* success *)
      subst t5. wp_cmpxchg_suc.
        replace (Z.of_nat t1 + 1)%Z with (Z.of_nat (S t1))...
        assert (t1 = t2)... subst t2.
        assert (t1 = t3)... subst t3. assert (t1 < b3) as Htb13...
        assert (t1 = t4)... subst t4. assert (t1 < b4) as Htb14...
        assert (t1 < b5) as Htb15...
        assert (mod_get l5 t1 = Some x) as Hx5.
        { replace (mod_get l5 t1) with (mod_get l4 t1)...
          apply Lb45... }
      iMod "AU" as (lau) "[Cont [_ Commit]]".
        iDestruct "Cont" as (γq' γpop' γcont' γglob') "[%Enc' ◯]".
        encode_agree Enc.
        iDestruct "Abst" as "(Glob & Q & Era)".
          iDestruct (own_ea_agree with "Q ◯") as "%Hlau". subst lau.
          rewrite (circ_slice_shrink_left _ _ _ x)...
          iMod (own_ea_update (circ_slice l5 (S t1) b5)
            with "Q ◯") as "[Q ◯]".
          iMod (some_auth_update with "Glob") as "Glob"...
        iCombine "Glob Q Era" as "Abst".
      iMod ("Commit" $! (circ_slice l5 (S t1) b5) (SOMEV x)
        with "[◯]") as "HΦ"; fr.
      iModIntro. iSplitL "Abst A Top Bot"; fr...
      wp_pures. iApply "HΦ"...
    - (* array was archived *)
      iDestruct "Abst" as "(Glob & Q & Era)".
        iDestruct (some_get_archived with "Glob F3")
          as (l' t' b') "#Arch"...
      iCombine "Glob Q Era" as "Abst".
        iDestruct (some_archived_get_lb with "Arch F3") as "%Ht3'".
        iDestruct (some_archived_get_frag with "Arch") as "F'".
        iDestruct (some_archived_get_circle with "Arch") as "PC".
        iAaccIntro with "[PC]".
        { unfold tele_app.
          instantiate (1:= {| tele_arg_head := l';
            tele_arg_tail := {| tele_arg_head := false |}
          |})... }
        all: simpl. { instantiate (1:=()). fr. fr. }
        simpl. iIntros (x) "[%Hx _]".
      iModIntro. iSplitL "Abst A Top Bot"; fr.
      wp_pures.

      (* 5. CAS *)
      wp_bind (CmpXchg _ _ _)%E.
      iInv "Inv" as (γcont5 era5 ca5 l5 t5 b5) "Invs".
        iDestruct "Invs" as "(>%Htb5 & >Abst & A & >Top & >Bot)".
        iDestruct "Abst" as "(Glob & Q & Era)".
          iDestruct (some_get_frag with "Glob") as "#F5".
          iDestruct (some_get_lb with "Glob F4") as "%Lb45".
          iDestruct (some_get_lb with "Glob F'") as "%Lb'5".
        iCombine "Glob Q Era" as "Abst".
      destruct (decide (t1 = t5)); last first.
      { (* fail *)
        wp_cmpxchg_fail. { intro NO. inversion NO... }
        iMod "AU" as (lau) "[Cont [_ Commit]]".
        iMod ("Commit" $! lau NONEV with "[Cont]") as "HΦ"...
        iModIntro. iSplitL "Abst A Top Bot"; fr.
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
        assert (mod_get l5 t1 = Some x) as Hx5.
        { replace (mod_get l5 t1) with (mod_get l' t1)...
          apply Lb'5... }
      iMod "AU" as (lau) "[Cont [_ Commit]]".
        iDestruct "Cont" as (γq' γpop' γcont' γglob') "[%Enc' ◯]".
        encode_agree Enc.
        iDestruct "Abst" as "(Glob & Q & Era)".
          iDestruct (own_ea_agree with "Q ◯") as "%Hlau". subst lau.
          rewrite (circ_slice_shrink_left _ _ _ x)...
          iMod (own_ea_update (circ_slice l5 (S t1) b5)
            with "Q ◯") as "[Q ◯]".
          iMod (some_auth_update with "Glob") as "Glob"...
        iCombine "Glob Q Era" as "Abst".
      iMod ("Commit" $! (circ_slice l5 (S t1) b5) (SOMEV x)
        with "[◯]") as "HΦ"; fr.
      iModIntro. iSplitL "Abst A Top Bot"; fr...
      wp_pures. iApply "HΦ"...
  Qed.
End proof.

(*
Program Definition atomic_deque `{!heapGS Σ, !dequeG Σ} :
  spec.atomic_deque Σ :=
  {| spec.new_deque_spec := new_deque_spec;
     spec.push_spec := push_spec;
     spec.pop_spec := pop_spec;
     spec.steal_spec := steal_spec;
     spec.deque_content_exclusive := deque_content_exclusive |}.

Global Typeclasses Opaque deque_content is_deque.
*)
