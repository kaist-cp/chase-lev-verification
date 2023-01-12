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
      (if: "t" + "sz" ≤ "b"
        then arr "deque" <- grow_circle "array"
        else #()
      ) ;;
      set_circle "array" "b" "v" ;;
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
    garrsG :> ghost_mapG Σ (gname * gname) (list val * nat * nat);
    gcasG :> ghost_mapG Σ (gname * gname) val;
    geltsG :> ghost_mapG Σ nat val;
    archiveG :> inG Σ mono_natR
  }.

Definition dequeΣ : gFunctors :=
  #[GFunctor (excl_authR $ listO valO);
    ghost_varΣ bool;
    mono_natΣ;
    ghost_mapΣ (gname * gname) (list val * nat * nat);
    ghost_mapΣ (gname * gname) val;
    ghost_mapΣ nat val;
    GFunctor mono_natR
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

  Definition top_bot_state (t b : nat) : nat :=
    2*t + (if bool_decide (t < b) then 1 else 0).

  Definition some_frag (γglob : gname*gname*gname*gname) (γcur : gname*gname)
  (ca : val) (l : list val) (t b : nat) : iProp :=
    let (γ', γt) := γglob in let (γ'', γelt) := γ' in let (γall, γarch) := γ'' in
    let (γcont, γtc) := γcur in
      ⌜length l ≠ 0⌝ ∗
      (* gname-local and global mono nats *)
      ( mono_nat_lb_own γt (top_bot_state t b) ∗
        mono_nat_lb_own γtc (top_bot_state t b)
      ) ∗
      (* top element preservation *)
      (⌜b ≤ t⌝ ∨ (∃ x, t ↪[γelt]□ x ∗ ⌜mod_get l t = Some x⌝)) ∗
      (* array archive *)
      γcur ↪[γall]□ ca.

  Definition some_archived (γglob : gname*gname*gname*gname) (γcur : gname*gname)
  (ca : val) (l : list val) (t b : nat) : iProp :=
    let (γ', γt) := γglob in let (γ'', γelt) := γ' in let (γall, γarch) := γ'' in
    let (γcont, γtc) := γcur in
      ⌜length l ≠ 0⌝ ∗
      (* gname-local and global mono nats *)
      ( mono_nat_lb_own γt (top_bot_state t b) ∗
        mono_nat_persistent γtc (top_bot_state t b)
      ) ∗
      (* top element preservation *)
      (⌜b ≤ t⌝ ∨ (∃ x, t ↪[γelt]□ x ∗ ⌜mod_get l t = Some x⌝)) ∗
      (* array archive *)
      ( γcur ↪[γall]□ ca ∗
        γcur ↪[γarch]□ (l, t, b) ∗
        persistent_circle ca l
      ).

  Definition some_auth (γglob : gname*gname*gname*gname) (γcur : gname*gname)
  (ca : val) (l : list val) (t b : nat) : iProp :=
    let (γ', γt) := γglob in let (γ'', γelt) := γ' in let (γall, γarch) := γ'' in
    let (γcont, γtc) := γcur in
    ∃ (allγ : gmap (gname * gname) val) (elts : gmap nat val)
    (archive : gmap (gname * gname) (list val * nat * nat)),
      ⌜length l ≠ 0⌝ ∗
      (* map ownership *)
      ( ghost_map_auth γall 1 allγ ∗
        ghost_map_auth γelt 1 elts ∗
        ghost_map_auth γarch 1 archive
      ) ∗
      (* gname-local and global mono nats *)
      ( mono_nat_auth_own γt 1 (top_bot_state t b) ∗
        mono_nat_auth_own γtc 1 (top_bot_state t b)
      ) ∗
      (* top element preservation *)
      ( ⌜∀ i, t < i → elts !! i = None⌝ ∗
        (⌜b ≤ t⌝ ∨ (∃ x, t ↪[γelt]□ x ∗ ⌜mod_get l t = Some x⌝))
      ) ∗
      (* array archive *)
      ( γcur ↪[γall]□ ca ∗
        [∗ map] γ ↦ ca' ∈ allγ, ⌜γ = γcur⌝ ∨ (
          ∃ l' t' b',
          some_archived γglob γ ca' l' t' b'
        )
      ).

  (* Timeless & Persistent *)
  Ltac desγ H1 H2 :=
    destruct H1 as (((γall,γarch),γelt),γt); destruct H2 as (γcont,γtc).
  
  Global Instance some_frag_timeless γglob γcur ca l t b :
    Timeless (some_frag γglob γcur ca l t b).
  Proof. desγ γglob γcur; apply _. Qed.

  Global Instance some_frag_persistent γglob γcur ca l t b :
    Persistent (some_frag γglob γcur ca l t b).
  Proof. desγ γglob γcur; apply _. Qed.
  
  Global Instance some_archived_timeless γglob γcur ca l t b :
    Timeless (some_archived γglob γcur ca l t b).
  Proof. desγ γglob γcur; apply _. Qed.

  Global Instance some_archived_persistent γglob γcur ca l t b :
    Persistent (some_archived γglob γcur ca l t b).
  Proof. desγ γglob γcur; apply _. Qed.

  Global Instance some_auth_timeless γglob γcur ca l t b :
    Timeless (some_auth γglob γcur ca l t b).
  Proof. desγ γglob γcur; apply _. Qed.
  
  Lemma top_bot_state_le t1 b1 t2 b2 :
    top_bot_state t1 b1 ≤ top_bot_state t2 b2 ↔
    t1 ≤ t2 ∧ (t1 = t2 ∧ t1 < b1 → t2 < b2).
  Proof. unfold top_bot_state. do 2 case_bool_decide; lia. Qed.

  Lemma some_auth_alloc γcont ca l t :
    length l ≠ 0 →
    ⊢ |==> ∃ (γglob : gname*gname*gname*gname) (γtc : gname),
      some_auth γglob (γcont, γtc) ca l t t.
  Proof.
    intros Hlen.

    (* gname-local and global mono nats *)
    iMod (mono_nat_own_alloc (top_bot_state t t)) as (γt) "[mono _]".
    iMod (mono_nat_own_alloc (top_bot_state t t)) as (γtc) "[monoc _]".

    (* map ownership *)
    iMod (ghost_map_alloc (
      <[(γcont, γtc) := ca]> (∅ : gmap (gname*gname) val))
      ) as (γall) "[All cur↪]".
      rewrite big_sepM_singleton.
      iMod (ghost_map_elem_persist with "cur↪") as "#cur↪".
    iMod (ghost_map_alloc
      (∅ : gmap nat val)
    ) as (γelt) "[Elts _]".
    iMod (ghost_map_alloc
      (∅ : gmap (gname*gname) (list val * nat * nat))
    ) as (γarch) "[Arch _]".

    iExists (γall, γarch, γelt, γt), γtc.
    iExists (<[(γcont, γtc) := ca]> ∅), ∅, ∅.
    iModIntro. fr. fr. rewrite big_sepM_singleton. fr.
  Qed.

  Lemma some_frag_get_nonzero γglob γcur ca l t b :
    some_frag γglob γcur ca l t b -∗ ⌜length l ≠ 0⌝.
  Proof. desγ γglob γcur. iIntros "(%Hlen & Mono & Elt & Ca)". auto. Qed.

  Lemma some_get_frag γglob γcur ca l t b :
    some_auth γglob γcur ca l t b -∗
    some_frag γglob γcur ca l t b.
  Proof.
    desγ γglob γcur.
    iIntros "Auth".
      iDestruct "Auth" as (allγ elts archive) "Auth".
      iDestruct "Auth" as "(%Hlen & Map & Mono & Elt & Ca)".
      iDestruct "Mono" as "[mono monoc]".
      iDestruct "Elt" as "[%NoElt Elt]".
      iDestruct "Ca" as "[↪ arch]".
    iDestruct (mono_nat_lb_own_get with "mono") as "#lb".
    iDestruct (mono_nat_lb_own_get with "monoc") as "#lbc".
    fr.
  Qed.

  Lemma some_get_archived γglob γ1 ca1 l1 t1 b1 γ2 ca2 l2 t2 b2 :
    (* γ1 is later than γ2 *)
    γ1 ≠ γ2 →
    some_auth γglob γ1 ca1 l1 t1 b1 -∗
    some_frag γglob γ2 ca2 l2 t2 b2 -∗
    ∃ l' t' b', some_archived γglob γ2 ca2 l' t' b'.
  Proof.
    desγ γglob γ1. destruct γ2 as (γcont', γtc').
    intros Hneq.
    iIntros "Auth".
      iDestruct "Auth" as (allγ elts archive) "Auth".
      iDestruct "Auth" as "(%Hlen & Map & Mono & Elt & Ca)".
    iIntros "Frag".
      iDestruct "Frag" as "(%Hlen' & Mono' & Elt' & Ca')".
    iDestruct "Map" as "(MapAll & MapElt & MapArch)".
      iDestruct (ghost_map_lookup with "MapAll Ca'") as "%Hγ2".
    iDestruct "Ca" as "[↪ arch]".
      iDestruct (big_sepM_lookup with "arch") as "sa"; eauto.
      iDestruct "sa" as "[%sa|sa]"; fr.
  Qed.

  Lemma some_get_lb γglob γ1 ca1 l1 t1 b1 γ2 ca2 l2 t2 b2 :
    (* γ1 is later than γ2 *)
    some_auth γglob γ1 ca1 l1 t1 b1 -∗
    some_frag γglob γ2 ca2 l2 t2 b2 -∗
    ⌜t2 ≤ t1 ∧ (
      (t2 = t1 ∧ t2 < b2) →
      (t1 < b1 ∧ mod_get l2 t2 = mod_get l1 t1)
    )⌝.
  Proof.
    desγ γglob γ1. destruct γ2 as (γcont', γtc').
    iIntros "Auth".
      iDestruct "Auth" as (allγ elts archive) "Auth".
      iDestruct "Auth" as "(%Hlen & Map & Mono & Elt & Ca)".
    iIntros "Frag".
      iDestruct "Frag" as "(%Hlen' & Mono' & Elt' & Ca')".
    iDestruct "Mono" as "[mono monoc]".
      iDestruct "Mono'" as "[lb lbc]".
      iDestruct (mono_nat_lb_own_valid with "mono lb") as "[_ %Hle]".
    apply top_bot_state_le in Hle as [Hle1 Hle2].
    iSplit. { iPureIntro; lia. }
    (* agreement proof *)
    iIntros ([-> Hlt2]).
    iSplit. { iPureIntro; lia. }
    iDestruct "Elt" as "[%NoElt [%Elt|Elt]]"; try lia.
      iDestruct "Elt" as (v1) "[Elt1 %Hget1]".
      iDestruct "Elt'" as "[%Elt'|Elt']"; try lia.
      iDestruct "Elt'" as (v2) "[Elt2 %Hget2]".
      iDestruct (ghost_map_elem_agree with "Elt1 Elt2") as "%". subst v2.
    iPureIntro. by rewrite Hget1 Hget2.
  Qed.

  Lemma some_archived_get_frag γglob γcur ca l t b :
    some_archived γglob γcur ca l t b -∗
    some_frag γglob γcur ca l t b.
  Proof.
    desγ γglob γcur.
    iIntros "Arch".
      iDestruct "Arch" as "(%Hlen & Mono & Elt & Ca)".
      iDestruct "Mono" as "[mono monoc]".
      iDestruct "Ca" as "[↪ Ca]".
    fr. fr.
    by iDestruct (mono_nat_persistent_lb_own_get with "monoc") as "lb".
  Qed.

  Lemma some_archived_get_lb γglob γcur ca l1 t1 b1 l2 t2 b2 :
    some_archived γglob γcur ca l1 t1 b1 -∗
    some_frag γglob γcur ca l2 t2 b2 -∗
    ⌜t2 ≤ t1 ∧ (
      (t2 = t1 ∧ t2 < b2) →
      (t1 < b1 ∧ mod_get l2 t2 = mod_get l1 t1)
    )⌝.
  Proof.
    desγ γglob γcur.
    iIntros "Arch".
      iDestruct "Arch" as "(%Hlen & Mono & Elt & Ca)".
    iIntros "Frag".
      iDestruct "Frag" as "(%Hlen' & Mono' & Elt' & Ca')".
    iDestruct "Mono" as "[mono monoc]".
      iDestruct "Mono'" as "[lb lbc]".
      iDestruct (mono_nat_persistent_lb_own_valid with "monoc lbc") as "%Hle".
    apply top_bot_state_le in Hle as [Hle1 Hle2].
    iSplit. { iPureIntro; lia. }
    (* agreement proof *)
    iIntros ([-> Hlt2]).
    iSplit. { iPureIntro; lia. }
    iDestruct "Elt" as "[%Elt|(%x & ↪x & %Hget)]"; try lia.
      iDestruct "Elt'" as "[%Elt|(%x' & ↪x' & %Hget')]"; try lia.
      iDestruct (ghost_map_elem_agree with "↪x ↪x'") as "%". subst x'.
    iPureIntro. by rewrite Hget Hget'.
  Qed.

  Lemma some_archived_get_circle γglob γcur ca l t b :
    some_archived γglob γcur ca l t b -∗
    persistent_circle ca l.
  Proof.
    desγ γglob γcur.
    iIntros "Arch".
      iDestruct "Arch" as "(%Hlen & Mono & Elt & Ca)".
    by iDestruct "Ca" as "(↪all & ↪arch & PC)".
  Qed.

  Lemma some_auth_update γglob γcur ca l t b :
    t < b →
    some_auth γglob γcur ca l t b ==∗
    some_auth γglob γcur ca l (S t) b.
  Proof.
    desγ γglob γcur.
    intros Htb.
    iIntros "Auth".
      iDestruct "Auth" as (allγ elts archive) "Auth".
      iDestruct "Auth" as "(%Hlen & Map & Mono & Elt & Ca)".

    (* update mono *)
    iDestruct "Mono" as "[mono monoc]".
      iMod (mono_nat_own_update
        (top_bot_state (S t) b) with "mono") as "[mono _]".
      { apply top_bot_state_le. lia. }
      iMod (mono_nat_own_update
        (top_bot_state (S t) b) with "monoc") as "[monoc _]".
      { apply top_bot_state_le. lia. }

    (* update top elt *)
    iDestruct "Elt" as "[%NoElt Elt]".
    iDestruct "Elt" as "[%Elt|(%x & ↪x & %Hget)]"; try lia.
    destruct (decide (S t < b)).
    - iDestruct "Map" as "(MapAll & MapElt & MapArch)".
      destruct (mod_get_is_Some l (S t)) as [v' HgetS]; auto.
      iMod (ghost_map_insert (S t) v' with "MapElt") as "[MapElt ↪S]".
      { apply NoElt. lia. }
      iMod (ghost_map_elem_persist with "↪S") as "#↪S".
      iModIntro. fr. fr.
      iPureIntro; intros i Sti.
      rewrite lookup_insert_ne; try lia. apply NoElt. lia.
    - iDestruct "Map" as "(MapAll & MapElt & MapArch)".
      iModIntro. fr. fr.
      + iPureIntro; intros i Sti. apply NoElt. lia.
      + iLeft. iPureIntro; lia.
  Qed.

  Lemma some_auth_archive γglob γcur ca l t b :
    own_circle ca -∗
    some_auth γglob γcur ca l t b ==∗
    some_archived γglob γcur ca l t b ∗
    ∃ γnew, some_auth γglob γnew ca l t b.
  Proof.
    desγ γglob γcur. iIntros "Own".
    iIntros "Auth".
      iDestruct "Auth" as (allγ elts archive) "Auth".
      iDestruct "Auth" as "(%Hlen & Map & Mono & Elt & Ca)".
      iDestruct "Elt" as "[NoElt Elt]".
      iDestruct "Ca" as "[↪ arch]".
(*
    (* archive circle *)
    iDestruct "Own" as (arr' l') "[%Hca Own]".
    
    (* archive γ *)
    iDestruct "Map" as "(MapAll & MapElt & MapArch)".
      iMod (ghost_map_insert γ (ca,l,t,b) with "MapArch") as "[Arch ↪arch]".
      1: admit.
      iMod (ghost_map_elem_persist with "↪arch") as "#↪arch".
    iDestruct "Mono" as "[mono monoc]".
      iDestruct (mono_nat_lb_own_get with "mono") as "#lb".
      iMod (mono_nat_own_persist with "monoc") as "#monoc".

    (* finish *)
    iModIntro. fr. fr.
    1: admit.
*)
  Admitted.
End some.

Section proof.
  Context `{!heapGS Σ, !dequeG Σ, !circleG Σ} (N : namespace).
  Notation iProp := (iProp Σ).

  Let circleN := N .@ "circle".
  Let dequeN := N .@ "deque".

  Definition deque_inv (γq γpop : gname) (γglob : gname*gname*gname*gname) (A top bot : loc) : iProp :=
    ∃ (γcont γcur : gname) (ca : val) (l : list val) (t b : nat),
      ⌜1 ≤ t ≤ b⌝ ∗
      some_auth γglob (γcont, γcur) ca l t b ∗
      own γq (●E (circ_slice l t b)) ∗
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
    ∃ (γq γpop : gname) (γglob : gname*gname*gname*gname) (A top bot : loc),
      ⌜q = (#A, #top, #bot)%V⌝ ∗
      ⌜γ = encode (γq, γpop, γglob)⌝ ∗
      inv dequeN (deque_inv γq γpop γglob A top bot).
  Global Instance is_deque_persistent γ q :
    Persistent (is_deque γ q) := _.

  Definition deque_content (γ : gname) (frag : list val) : iProp :=
    ∃ (γq γpop : gname) (γglob : gname*gname*gname*gname),
      ⌜γ = encode (γq, γpop, γglob)⌝ ∗
      own γq (◯E frag).
  Global Instance deque_content_timeless γ frag :
    Timeless (deque_content γ frag) := _.

  (* owner of the deque who can call push and pop *)
  Definition own_deque (γ : gname) (q : val) : iProp :=
    ∃ (γq γpop : gname) (γglob : gname*gname*gname*gname) (ca : val) (A top bot : loc) (b : nat),
      ⌜γ = encode (γq, γpop, γglob)⌝ ∗
      ⌜q = (#A, #top, #bot)%V⌝ ∗
      (* own circle *)
      A ↦{#1/2} ca ∗ own_circle ca ∗
      (* own bottom *)
      bot ↦{#1/2} #b ∗ ghost_var γpop (1/2) false.
  
  Lemma deque_content_exclusive γ frag1 frag2 :
    deque_content γ frag1 -∗ deque_content γ frag2 -∗ False.
  Proof.
    iIntros "C1 C2".
      iDestruct "C1" as (γq γpop γglob) "[%Enc C1]".
      iDestruct "C2" as (γq' γpop' γglob') "[%Enc' C2]".
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
    iIntros (γcont ca l) "!> (%Len & IC & 🎯 & Ⓜ️)". wp_pures.
    wp_alloc bot as "[b↦1 b↦2]". wp_alloc top as "t↦".
    wp_alloc A as "[A↦1 A↦2]". wp_pures.

    (* make resources *)
    iMod (own_alloc (●E [] ⋅ ◯E [])) as (γq) "[γq● γq◯]".
      1: apply excl_auth_valid.
    iMod (ghost_var_alloc false) as (γpop) "[γpop1 γpop2]".
    iMod (some_auth_alloc γcont ca l 1) as (γglob γcur) "Auth"...
    iMod (inv_alloc dequeN _ (deque_inv γq γpop γglob A top bot)
      with "[A↦1 t↦ b↦1 IC 🎯 γq● γpop1 Auth]") as "Inv".
    { fr. fr. }

    (* apply Φ *)
    iApply "HΦ". iModIntro. iSplitL "Inv"; first fr.
    iSplitL "γq◯"; first fr. fr. fr. instantiate (1:=1)...
  Qed.

  Lemma push_spec γ q (v : val) :
    is_deque γ q -∗
    own_deque γ q -∗
    <<< ∀∀ l : list val, deque_content γ l >>>
      push q v @ ↑N
    <<< deque_content γ (l ++ [v]),
      RET #(), own_deque γ q >>>.
  Proof with extended_auto.
    iIntros "#Inv Own" (Φ) "AU".
      iDestruct "Own" as (γq γpop γglob ca A top bot b) "(%Enc & %Q & AOwn & caOwn & bOwn & popOwn)".
        subst q.
      iDestruct "Inv" as (γq' γpop' γglob' A' top' bot') "(%Q' & %Enc' & Inv)".
        injection Q' as [= <- <- <-]. encode_agree Enc.
    wp_lam. unfold code.arr, code.top, code.bot. wp_pures.

    (* load bot *)
    wp_load. wp_pures.

    (* 1. load top *)
    wp_bind (! _)%E.
      iInv "Inv" as (γcont γ1 ca1 l1 t1 b1) "(>%Htb1 & >Auth & >● & A & >Top & >Bot)".
        iDestruct "A" as "(>A↦ & #🎯1 & >📚)".
          iDestruct (mapsto_agree with "AOwn A↦") as "%". subst ca1.
        iCombine "A↦ 🎯1 📚" as "A".
        wp_load.
      iModIntro. iSplitL "Auth ● A Top Bot"; fr.
    wp_pures.
    wp_load. wp_pures.

    (* 2. get size *)
    wp_bind (size_circle _)%E.
      awp_apply size_circle_spec...
      iInv "Inv" as (γc2 γ2 ca2 l2 t2 b2) "(>%Htb2 & >Auth & >● & A & >Top & >Bot)".
        iDestruct "A" as "(>A↦ & #🎯2 & >📚)".
          iDestruct (mapsto_agree with "AOwn A↦") as "%". subst ca2.
      iAaccIntro with "[📚]".

    iInv "Inv" as (γC4 γ4 ca4 l4 t4 b4) "(>%Htb4 & >Auth & >● & A & >Top & >Bot)".
      iDestruct (some_get_frag with "Auth") as "#F4".
      iDestruct (some_get_lb with "Auth F3") as "%Lb34".
      iDestruct "A" as "(>A↦ & #🎯4 & >📚)".
    
    destruct (decide (γC3 = γC4)) as [eqγ|neqγ].
    - (* array was not archived *)
      subst γC4.
      iAaccIntro with "[📚]".
      { unfold tele_app.
        instantiate (1:= {| tele_arg_head := l4;
          tele_arg_tail := {| tele_arg_head := true |}
        |})... }
        all: simpl. { instantiate (1:=()). fr. fr. }
        simpl. iIntros (x) "[%Hx 📚]".
        iCombine "A↦ 🎯4 📚" as "A".
      iModIntro. iSplitL "Auth ● A Top Bot"; fr.
      
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
    iIntros "#Inv" (Φ) "AU".
      iDestruct "Inv" as (γq γpop γglob A top bot) "(%Q & %Enc & Inv)".
      subst q.
    wp_lam. unfold code.arr, code.top, code.bot. wp_pures.

    (* 1. load top *)
    wp_bind (! _)%E.
    iInv "Inv" as (γC1 γ1 ca1 l1 t1 b1) "(>%Htb1 & >Auth & >● & A & >Top & >Bot)".
      iDestruct (some_get_frag with "Auth") as "#F1".
      wp_load.
    iModIntro. iSplitL "Auth ● A Top Bot"; fr.
    wp_pures.

    (* 2. load bot *)
    wp_bind (! _)%E.
    iInv "Inv" as (γC2 γ2 ca2 l2 t2 b2) "(>%Htb2 & >Auth & >● & A & >Top & >Bot)".
      iDestruct (some_get_frag with "Auth") as "#F2".
      iDestruct (some_get_lb with "Auth F1") as "%Lb12".
      iDestruct "Bot" as (Pop2) "[bot↦ Pop]". wp_load.
      iCombine "bot↦ Pop" as "Bot".
    iModIntro. iSplitL "Auth ● A Top Bot"; fr.
    wp_pures.

    (* 3. load array *)
    wp_alloc arr as "arr↦". wp_pures.
    wp_bind (! _)%E.
    iInv "Inv" as (γC3 γ3 ca3 l3 t3 b3) "(>%Htb3 & >Auth & >● & A & >Top & >Bot)".
      iDestruct (some_get_frag with "Auth") as "#F3".
      iDestruct (some_get_lb with "Auth F2") as "%Lb23".
      iDestruct "A" as "(>A↦ & #🎯3 & >📚)". wp_load.
      iCombine "A↦ 🎯3 📚" as "A".
    iModIntro. iSplitL "Auth ● A Top Bot"; fr.
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
    iInv "Inv" as (γC4 γ4 ca4 l4 t4 b4) "(>%Htb4 & >Auth & >● & A & >Top & >Bot)".
      iDestruct (some_get_frag with "Auth") as "#F4".
      iDestruct (some_get_lb with "Auth F3") as "%Lb34".
      iDestruct "A" as "(>A↦ & #🎯4 & >📚)".
    
    destruct (decide (γC3 = γC4)) as [eqγ|neqγ].
    - (* array was not archived *)
      subst γC4.
      iAaccIntro with "[📚]".
      { unfold tele_app.
        instantiate (1:= {| tele_arg_head := l4;
          tele_arg_tail := {| tele_arg_head := true |}
        |})... }
        all: simpl. { instantiate (1:=()). fr. fr. }
        simpl. iIntros (x) "[%Hx 📚]".
        iCombine "A↦ 🎯4 📚" as "A".
      iModIntro. iSplitL "Auth ● A Top Bot"; fr.
      wp_pures.
      
      (* 5. CAS *)
      wp_bind (CmpXchg _ _ _)%E.
      iInv "Inv" as (γC5 γ5 ca5 l5 t5 b5) "(>%Htb5 & >Auth & >● & A & >Top & >Bot)".
        iDestruct (some_get_frag with "Auth") as "#F5".
        iDestruct (some_get_lb with "Auth F4") as "%Lb45".
      destruct (decide (t1 = t5)); last first.
      { (* fail *)
        wp_cmpxchg_fail. { intro NO. inversion NO... }
        iMod "AU" as (lau) "[Cont [_ Commit]]".
        iMod ("Commit" $! lau NONEV with "[Cont]") as "HΦ"...
        iModIntro. iSplitL "Auth ● A Top Bot"; fr.
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
          iDestruct "Cont" as (γq' γpop' γglob') "[%Enc' ◯]".
          encode_agree Enc.
          iDestruct (own_ea_agree with "● ◯") as "%Hlau". subst lau.
          iDestruct (some_frag_get_nonzero with "F5") as "%nonzero5".
          rewrite (circ_slice_shrink_left _ _ _ x)...
          iMod (own_ea_update (circ_slice l5 (S t1) b5) with "● ◯") as "[● ◯]".
          iMod (some_auth_update with "Auth") as "Auth"...
        iMod ("Commit" $! (circ_slice l5 (S t1) b5) (SOMEV x) with "[◯]") as "HΦ"; fr.
      iModIntro. iSplitL "Auth ● A Top Bot"; fr...
      wp_pures. iApply "HΦ"...
    - (* array was archived *)
      iDestruct (some_get_archived with "Auth F3") as (l' t' b') "#Arch".
        { intro NO. injection NO... }
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
        iCombine "A↦ 🎯4 📚" as "A".
      iModIntro. iSplitL "Auth ● A Top Bot"; fr.
      wp_pures.

      (* 5. CAS *)
      wp_bind (CmpXchg _ _ _)%E.
      iInv "Inv" as (γC5 γ5 ca5 l5 t5 b5) "(>%Htb5 & >Auth & >● & A & >Top & >Bot)".
        iDestruct (some_get_frag with "Auth") as "#F5".
        iDestruct (some_get_lb with "Auth F4") as "%Lb45".
        iDestruct (some_get_lb with "Auth F'") as "%Lb'5".
      destruct (decide (t1 = t5)); last first.
      { (* fail *)
        wp_cmpxchg_fail. { intro NO. inversion NO... }
        iMod "AU" as (lau) "[Cont [_ Commit]]".
        iMod ("Commit" $! lau NONEV with "[Cont]") as "HΦ"...
        iModIntro. iSplitL "Auth ● A Top Bot"; fr.
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
          iDestruct "Cont" as (γq' γpop' γglob') "[%Enc' ◯]".
          encode_agree Enc.
          iDestruct (own_ea_agree with "● ◯") as "%Hlau". subst lau.
          iDestruct (some_frag_get_nonzero with "F5") as "%nonzero5".
          rewrite (circ_slice_shrink_left _ _ _ x)...
          iMod (own_ea_update (circ_slice l5 (S t1) b5) with "● ◯") as "[● ◯]".
          iMod (some_auth_update with "Auth") as "Auth"...
        iMod ("Commit" $! (circ_slice l5 (S t1) b5) (SOMEV x) with "[◯]") as "HΦ"; fr.
      iModIntro. iSplitL "Auth ● A Top Bot"; fr...
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
