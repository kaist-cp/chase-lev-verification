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
(*\
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

(*
  Lemma some_auth_archive γglob γ ca l t b :
    own_circle ca -∗
    some_auth γglob γ ca l t b ==∗
    some_archived γglob γ ca l t b.
    (*
    ∃ γ',
      some_auth γglob γ' ca l t b ∗ some_archived γglob γ ca l t b.
      *)
  Proof.
    destruct γglob as (((γall,γarch),γelt),γt).
    iIntros "Own".
    iIntros "Auth".
      iDestruct "Auth" as (allγ elts archive) "Auth".
      iDestruct "Auth" as "(%Hlen & Map & Mono & Elt & Ca)".
      iDestruct "Elt" as "[NoElt Elt]".
      iDestruct "Ca" as "[↪ arch]".

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
  Admitted.
*)
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
      iDestruct "Own" as (γq γpop γglob l A arr top bot b)
        "(%Enc & -> & γOwn & AOwn & arrOwn & bOwn)".
      iDestruct "Inv" as (A' top' bot') "[%Q Inv]".
      injection Q as [= <- <- <-].
    wp_lam. unfold code.arr, code.top, code.bot. wp_pures.

    (* load A & bot *)
    wp_load. wp_pures.
    wp_load. wp_pures.

    (* load top *)
    wp_bind (! _)%E.
      iInv "Inv" as (γq' γpop' γglob' l1 Pop1 arr1 t1 b1)
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
      iInv "Inv" as (γq' γpop' γglob' l2 Pop2 arr2 t2 b2)
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
    iInv "Inv" as (γq' γpop' γglob' l3 Pop3 arr3 t3 b3)
        ">(%Enc' & %Bound3 & Phys & Abst & Mono)".
        encode_agree Enc.
      iMod "AU" as (q) "[Cont [_ Commit]]".
        iDestruct "Cont" as (γq' γpop' γglob') "[%Enc' ◯]".
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
      iDestruct "Own" as (γq γpop γglob l A arr top bot b)
        "(%Enc & -> & γOwn & AOwn & arrOwn & bOwn)".
      iDestruct "Inv" as (A' top' bot') "[%Q Inv]".
      injection Q as [= <- <- <-].
    wp_lam. unfold code.arr, code.top, code.bot. wp_pures.

    (* load arr & bot *)
    wp_load. wp_pures.
    wp_load. wp_pures.

    (* decrement b early *)
    wp_bind (_ <- _)%E.
      iInv "Inv" as (γq' γpop' γglob' l1 Pop1 arr1 t1 b1)
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
      iInv "Inv" as (γq' γpop' γglob' l2 Pop2 arr2 t2 b2)
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
        iDestruct "Cont" as (γq' γpop' γglob') "[%Enc' ◯]".
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
      iInv "Inv" as (γq' γpop' γglob' l3 Pop3 arr3 t3 b3)
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
      iInv "Inv" as (γq' γpop' γglob' l3 Pop3 arr3 t3 b3)
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
        iDestruct "Cont" as (γq' γpop' γglob') "[%Enc' ◯]".
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

      iInv "Inv" as (γq' γpop' γglob' l4 Pop4 arr4 t4 b4)
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
      iInv "Inv" as (γq' γpop' γglob' l4 Pop4 arr4 t4 b4)
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
