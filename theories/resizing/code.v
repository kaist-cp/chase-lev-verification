From iris.algebra Require Import list excl_auth mono_nat.
From iris.bi Require Import derived_laws_later.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import invariants ghost_var.
From chase_lev Require Import mono_list mono_nat atomic.
From iris.heap_lang Require Import proofmode notation.
From iris.prelude Require Import options.
From chase_lev.resizing Require Import helpers spec.

Section grow.
  Context `{!heapGS Σ} (N : namespace).
  Definition circ_access : val :=
    λ: "arr" "i" "n",
      "arr" +ₗ ("i" `rem` "n").

  Definition grow_circle_rec : val :=
    rec: "grow_rec" "arr" "sz" "narr" "nsz" "t" "b" :=
      if: "t" < "b"
      then (
        let: "b'" := "b" - #1 in
        let: "v" := !(circ_access "arr" "b'" "sz") in
        (circ_access "narr" "b'" "nsz") <- "v" ;;
        "grow_rec" "circle" "ncirc" "t" "b'"
      )
      else #().
  
  Definition grow_circle : val :=
    λ: "circle" "t" "b",
      let: "sz" := Snd "circle" in
      let: "nsz" := #2 * "sz" in
      let: "narr" := AllocN "nsz" #0 in
      grow_circle_rec (Fst "circle") "sz" "narr" "nsz" "t" "b" ;;
      ("narr", "nsz").

      (*
  Lemma grow_circle_rec_spec (arr arr' : loc)
  (l l' : list val) (n m t b : nat) :
    True -∗
    <<< ∀∀ (l : list val), ⌜length l = n⌝ ∗ arr ↦∗ l >>>
      grow_circle_rec #arr #n #arr' #m #t #b @ ↑N
    <<< ∃∃ (l' : list val),
      ⌜length l' = m⌝ ∗ arr' ↦∗ l',
      RET #()
    >>>.
      Lemma grow_circle_rec_spec γ ca l
  (arr' : loc) (l' : list val) (t b : nat) :
    0 < length l ≤ length l' →
    t ≤ b < t + length l →
    is_circle γ ca -∗ own_circle ca l -∗
    arr' ↦∗ l' -∗
    <<< ∀∀ (_ : ()), circle_content γ l >>>
      grow_circle_rec ca (#arr', #(length l'))%V #t #b @ ↑N
    <<< ∃∃ (l2' : list val),
      ⌜length l' = length l2'⌝ ∗
      ⌜circ_slice l t b = circ_slice l2' t b⌝ ∗
      ⌜∀ i, b ≤ i < t + length l → mod_get l' i = mod_get l2' i⌝ ∗
      circle_content γ l,
    RET #(), own_circle ca l ∗ arr' ↦∗ l2' >>>.
    *)
  
  Lemma grow_circle_spec (arr : loc) (l : list val) (t b : nat) :
    0 < length l →
    t ≤ b < t + length l → ⊢
    <<< ∀∀ (_ : ()), arr ↦∗ l >>>
      grow_circle (#arr, #(length l))%V #t #b @ ∅
    <<< ∃∃ (arr' : loc) (l' : list val),
      ⌜length l < length l'⌝ ∗
      ⌜circ_slice l t b = circ_slice l' t b⌝ ∗
      arr ↦∗ l ∗ arr' ↦∗ l',
    RET (#arr', #(length l')) >>>.
  Admitted.
End grow.

Section code.


  Definition new_deque : val :=
    λ: "sz",
      let: "array" := AllocN "sz" #0 in
      (ref ("array", "sz"), ref #1, ref #1). (* array+size, top, bot *)
  
  Definition arr : val := λ: "deque", Fst (Fst "deque").
  Definition top : val := λ: "deque", Snd (Fst "deque").
  Definition bot : val := λ: "deque", Snd "deque".

  Definition push : val :=
    λ: "deque" "v",
      let: "b" := !(bot "deque") in
      let: "t" := !(top "deque") in
      let: "circle" := !(arr "deque") in
      let: "sz" := Snd "circle" in
      (if: "t" + "sz" ≤ "b" + #1
        then arr "deque" <- grow_circle "circle" "t" "b"
        else #()
      ) ;;
      (circ_access (Fst "circle") "b" "sz") <- "v" ;;
      bot "deque" <- "b" + #1.
  
  Definition pop : val :=
    λ: "deque",
      let: "b" := !(bot "deque") - #1 in
      let: "circle" := !(arr "deque") in
      let: "sz" := Snd "circle" in
      bot "deque" <- "b" ;;
      let: "t" := !(top "deque") in
      if: "b" < "t" then (* empty pop *)
        bot "deque" <- "t" ;; NONE
      else let: "v" := !(circ_access (Fst "circle") "b" "sz") in
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
      let: "circle" := !(arr "deque") in
      let: "sz" := Snd "circle" in
      if: "b" ≤ "t" then NONE (* no chance *)
      else let: "v" := !(circ_access (Fst "circle") "t" "sz") in
      if: CAS (top "deque") "t" ("t" + #1)
      then SOME "v" (* success *)
      else NONE. (* fail *)
End code.

(** Ghost state for the deque *)

Class dequeG Σ := DequeG {
    (* invariant *)
    deque_tokG :> inG Σ (excl_authR $ listO valO);
    deque_popG :> ghost_varG Σ bool;
    eraG :> ghost_varG Σ (nat * list val);
    (* RA *)
    topbotG :> mono_natG Σ;
    topeltG :> mono_listG val Σ;
    roomG :> mono_listG (gname * loc) Σ;
    museumG :> mono_listG (list val * nat * nat) Σ
  }.

Definition dequeΣ : gFunctors :=
  #[ (*invariant *)
    GFunctor (excl_authR $ listO valO);
    ghost_varΣ bool;
    ghost_varΣ (nat * list val);
    (* RA *)
    mono_natΣ;
    mono_listΣ val;
    mono_listΣ (gname * loc);
    mono_listΣ (list val * nat * nat)
  ].

Global Instance subG_dequeΣ {Σ} : subG dequeΣ Σ → dequeG Σ.
Proof. solve_inG. Qed.

Local Ltac extended_auto :=
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
Local Ltac fr :=
  repeat iIntros; repeat iSplit; extended_auto;
  repeat iIntros; repeat iExists _;
  try iFrame "arr↦"; try iFrame "arr↦1"; try iFrame "arr↦2"; 
  iFrame; eauto.

Section dqst.
  Context `{!heapGS Σ, !dequeG Σ}.
  Notation iProp := (iProp Σ).
  Definition glob_gnames : Type := gname*gname*gname*gname.

  Definition top_bot_state (t b : nat) : nat :=
    2*t + (if bool_decide (t < b) then 1 else 0).

  Definition dqst_frag (γglob : glob_gnames) (era : nat)
  (arr : loc) (l : list val) (t b : nat) : iProp :=
    let (γ'              , γmus) := γglob in
    let (γ''      , γroom) := γ' in
    let (γtb, γelt) := γ'' in
    ∃ (γtbe : gname),
    ⌜1 ≤ t ≤ b ∧ b < t + length l ∧ length l ≠ 0⌝ ∗
    (* top-bot profile *)
    ( mono_nat_lb_own γtb (top_bot_state t b) ∗
      mono_nat_lb_own γtbe (top_bot_state t b)
    ) ∗
    (* top element preservation *)
    ( ∃ (elts : list val),
      mono_list_lb_own γelt elts ∗
      ⌜t = b ∨ mod_get l t = elts !! t⌝
    ) ∗
    (* museum of past gnames and circles *)
    ( ∃ (room : list (gname * loc)),
      ⌜room !! era = Some (γtbe, arr)⌝ ∗
      mono_list_lb_own γroom room
    ).

  Definition dqst_archived (γglob : glob_gnames) (era : nat)
  (arr : loc) (l : list val) (t b : nat) : iProp :=
    let (γ'              , γmus) := γglob in
    let (γ''      , γroom) := γ' in
    let (γtb, γelt) := γ'' in
    ∃ (γtbe : gname),
    ⌜1 ≤ t ≤ b ∧ b < t + length l ∧ length l ≠ 0⌝ ∗
    (* top-bot profile *)
    ( mono_nat_lb_own γtb (top_bot_state t b) ∗
      mono_nat_persistent γtbe (top_bot_state t b)
    ) ∗
    (* top element preservation *)
    ( ∃ (elts : list val),
      mono_list_lb_own γelt elts ∗
      ⌜t = b ∨ mod_get l t = elts !! t⌝
    ) ∗
    (* museum of past gnames and circles *)
    ( ∃ (room : list (gname * loc))
        (museum : list (list val * nat * nat)),
      ⌜room !! era = Some (γtbe, arr)⌝ ∗
      ⌜museum !! era = Some (l, t, b)⌝ ∗
      mono_list_lb_own γroom room ∗
      mono_list_lb_own γmus museum
    ) ∗
    (* persistent circle *)
    arr ↦∗□ l.

  Definition dqst_auth (γglob : glob_gnames) (era : nat)
  (arr : loc) (l : list val) (t b : nat) : iProp :=
    let (γ'              , γmus) := γglob in
    let (γ''      , γroom) := γ' in
    let (γtb, γelt) := γ'' in
    ∃ (γtbe : gname),
    ⌜1 ≤ t ≤ b ∧ b < t + length l ∧ length l ≠ 0⌝ ∗
    (* top-bot profile *)
    (mono_nat_auth_own γtb 1 (top_bot_state t b) ∗
      mono_nat_auth_own γtbe 1 (top_bot_state t b)
    ) ∗
    (* top element preservation *)
    (∃ (elts : list val),
      mono_list_auth_own γelt 1 elts ∗
      ⌜if (bool_decide (t = b))
        then length elts = t
        else (length elts = S t ∧ mod_get l t = elts !! t)⌝
    ) ∗
    (* museum of past gnames and circles *)
    ( ∃ (proom : list (gname * loc))
        (museum : list (list val * nat * nat)),
      ⌜length proom = era ∧ length museum = era⌝ ∗
      mono_list_auth_own γroom 1 (proom ++ [(γtbe, arr)]) ∗
      mono_list_auth_own γmus 1 museum ∗
      [∗ list] i ↦ gc ; ltbi ∈ proom ; museum, (
        dqst_archived γglob i (gc.2) (ltbi.1.1) (ltbi.1.2) (ltbi.2)
      )
    ).

  (* Timeless & Persistent *)
  Ltac desγ H :=
    destruct H as (((γtb, γelt), γroom), γmuseum).

  Global Instance dqst_frag_timeless γglob era ca l t b :
    Timeless (dqst_frag γglob era ca l t b).
  Proof. desγ γglob. apply _. Qed.

  Global Instance dqst_frag_persistent γglob era ca l t b :
    Persistent (dqst_frag γglob era ca l t b).
  Proof. desγ γglob. apply _. Qed.
  
  Global Instance dqst_archived_timeless γglob era ca l t b :
    Timeless (dqst_archived γglob era ca l t b).
  Proof. desγ γglob. apply _. Qed.

  Global Instance dqst_archived_persistent γglob era ca l t b :
    Persistent (dqst_archived γglob era ca l t b).
  Proof. desγ γglob. apply _. Qed.

  Global Instance dqst_auth_timeless γglob era ca l t b :
    Timeless (dqst_auth γglob era ca l t b).
  Proof. desγ γglob. apply _. Qed.
  
  Lemma top_bot_state_le t1 b1 t2 b2 :
    top_bot_state t1 b1 ≤ top_bot_state t2 b2 ↔
    t1 ≤ t2 ∧ (t1 = t2 ∧ t1 < b1 → t2 < b2).
  Proof. unfold top_bot_state. do 2 case_bool_decide; lia. Qed.

  Lemma dqst_auth_alloc ca l :
    length l ≠ 0 →
    ⊢ |==> ∃ (γglob : glob_gnames),
      dqst_auth γglob 0 ca l 1 1.
  Proof.
    intros Hl. unfold dqst_auth.
    iMod (mono_nat_own_alloc 2) as (γtb) "[tb _]".
    iMod (mono_nat_own_alloc 2) as (γtbe) "[tbe _]".
    iMod (mono_list_own_alloc ([NONEV])) as (γelt) "[topelt _]".
    iMod (mono_list_own_alloc ([(γtbe, ca)])) as (γroom) "[room _]".
    iMod (mono_list_own_alloc ([] : list (list val * nat * nat))) as (γmus) "[museum _]".
    iExists (γtb, γelt, γroom, γmus).
    iModIntro. fr. fr.
    iSplitL "topelt"; fr. fr.
  Qed.

  Lemma dqst_frag_agree γglob era ca1 l1 t1 b1 ca2 l2 t2 b2 :
    dqst_frag γglob era ca1 l1 t1 b1 -∗
    dqst_frag γglob era ca2 l2 t2 b2 -∗
    ⌜ca1 = ca2⌝.
  Proof.
    desγ γglob.
    iIntros "F1 F2".
      iDestruct "F1" as (γtbe1) "(%Hlt1 & tb1 & elt1 & muse1)".
      iDestruct "muse1" as (room1) "[%Hroom1 Lb1]".
      iDestruct "F2" as (γtbe2) "(%Hlt2 & tb2 & elt2 & muse2)".
      iDestruct "muse2" as (room2) "[%Hroom2 Lb2]".
    iDestruct (mono_list_lb_valid with "Lb1 Lb2") as "[%Pref|%Pref]".
    - eapply prefix_lookup in Hroom1; eauto.
      rewrite Hroom2 in Hroom1. by injection Hroom1.
    - eapply prefix_lookup in Hroom2; eauto.
      rewrite Hroom2 in Hroom1. by injection Hroom1.
  Qed.

  Lemma dqst_get_frag γglob era ca l t b :
    dqst_auth γglob era ca l t b -∗
    dqst_frag γglob era ca l t b.
  Proof with extended_auto.
    desγ γglob.
    iIntros "Auth".
      iDestruct "Auth" as (γtbeO) "(%HltO & [tbO tbeO] & eltO & museO)".
      iDestruct "eltO" as (elts) "[Elt %Heltslen]".
      iDestruct "museO" as (room museum) "museO".
      iDestruct "museO" as "([%Hroomlen %Hmuslen] & museO)".
      iDestruct "museO" as "(Room & Museum & Archives)".
    iDestruct (mono_nat_lb_own_get with "tbO") as "#lb".
    iDestruct (mono_nat_lb_own_get with "tbeO") as "#lbe".
    iDestruct (mono_list_lb_own_get with "Elt") as "#eltlb".
    iDestruct (mono_list_lb_own_get with "Room") as "#rlb".
    fr. fr.
    - fr. case_bool_decide; [iLeft|iRight]... destruct Heltslen...
    - fr. rewrite lookup_app_r... replace (era - length room) with 0...
  Qed.

  Lemma dqst_get_archived γglob era1 ca1 l1 t1 b1
  era2 ca2 l2 t2 b2 :
    (* era1 is later than era2 *)
    era1 ≠ era2 →
    dqst_auth γglob era1 ca1 l1 t1 b1 -∗
    dqst_frag γglob era2 ca2 l2 t2 b2 -∗
    ∃ l' t' b', dqst_archived γglob era2 ca2 l' t' b'.
  Proof with extended_auto.
    desγ γglob.
    iIntros (Hneq) "Auth F".
      iDestruct "Auth" as (γtbeO) "(%HltO & tbO & eltO & museO)".
      iDestruct "museO" as (room museum) "museO".
      iDestruct "museO" as "([%Hroomlen %Hmuslen] & museO)".
      iDestruct "museO" as "(Room & Museum & Archives)".
      iDestruct "F" as (γtbe) "(%Hlt & tb & elt & muse)".
      iDestruct "muse" as (room') "[%Hroom'2 Lb']".
    iDestruct (mono_list_auth_lb_valid with "Room Lb'") as "%Pref".
      destruct Pref as [_ Pref].
      eapply prefix_lookup in Hroom'2; eauto.
    assert (era2 < era1) as Hera21.
    { apply lookup_lt_Some in Hroom'2.
      rewrite app_length Hroomlen in Hroom'2. simpl in Hroom'2... }
    assert (is_Some (museum !! era2)) as [ltbera2 Hltbera2].
    { rewrite lookup_lt_is_Some... }
    rewrite lookup_app_l in Hroom'2...
    iDestruct (big_sepL2_lookup with "Archives") as "Arch2"...
  Qed.

  Lemma dqst_get_lb γglob era1 ca1 l1 t1 b1
  era2 ca2 l2 t2 b2 :
    (* era1 is later than era2 *)
    dqst_auth γglob era1 ca1 l1 t1 b1 -∗
    dqst_frag γglob era2 ca2 l2 t2 b2 -∗
    ⌜t2 ≤ t1 ∧ (
      (t2 = t1 ∧ t2 < b2) →
      (t1 < b1 ∧ mod_get l2 t2 = mod_get l1 t1)
    )⌝.
  Proof with extended_auto.
    desγ γglob.
    iIntros "Auth F".
      iDestruct "Auth" as (γtbeO) "(%HltO & [tbO tbeO] & eltO & museO)".
      iDestruct "F" as (γtbe) "(%Hlt & [tb tbe] & elt & muse)".
    iDestruct (mono_nat_lb_own_valid with "tbO tb") as "[_ %Htb]".
      apply top_bot_state_le in Htb as [Ht21 Htb21]. fr.
    iIntros ([H1 Ht1b2]). subst t2. assert (t1 < b1) as Htb1... fr.
    iDestruct "elt" as (elts') "[lb %Helts]"...
      destruct Helts as [NO|Helts]...
      iDestruct "eltO" as (elts) "[Elts %Heltslen]".
      iDestruct (mono_list_auth_lb_lookup t1 with "Elts lb") as "%Heqg"...
      { rewrite -lookup_lt_is_Some -Helts. apply mod_get_is_Some... }
      iDestruct (mono_list_auth_lb_valid with "Elts lb") as "[_ %Pref]".
      case_bool_decide... destruct Heltslen as [_ Hget].
    rewrite Hget Helts...
  Qed.

  Lemma dqst_archived_get_frag γglob era ca l t b :
    dqst_archived γglob era ca l t b -∗
    dqst_frag γglob era ca l t b.
  Proof.
    desγ γglob.
    iIntros "Arc".
      iDestruct "Arc" as (γtbeA) "(%Hlt & [tb tbe] & elt & muse & pers)".
      iDestruct "muse" as (room museum) "(%Hroom & Hmuseum & Room & Museum)".
    fr. fr. by iApply mono_nat_persistent_lb_own_get.
  Qed.

  Lemma dqst_archived_get_lb γglob era ca l1 t1 b1 l2 t2 b2 :
    dqst_archived γglob era ca l1 t1 b1 -∗
    dqst_frag γglob era ca l2 t2 b2 -∗
    ⌜t2 ≤ t1 ∧ (
      (t2 = t1 ∧ t2 < b2) →
      (t1 < b1 ∧ mod_get l2 t2 = mod_get l1 t1)
    )⌝.
  Proof with extended_auto.
    desγ γglob.
    iIntros "Arc F".
      iDestruct "Arc" as (γtbeA) "(%Hlt1 & [tb1 tbe1] & elt1 & muse1 & pers1)".
      iDestruct "muse1" as (room1 museum1) "muse1".
      iDestruct "muse1" as "(%Hroom1 & %Hmuse1 & Lbroom1 & Lbmuse1)".
      iDestruct "F" as (γtbe) "(%Hlt2 & [tb2 tbe2] & elt2 & muse2)".
      iDestruct "muse2" as (room2) "[%Hroom2 Lbroom2]".
    iDestruct (mono_list_lb_lookup era with "Lbroom1 Lbroom2") as "%Hr12".
      { apply lookup_lt_Some in Hroom1... }
      { apply lookup_lt_Some in Hroom2... }
      rewrite Hroom1 Hroom2 in Hr12. injection Hr12 as [= <-].
    iDestruct (mono_nat_persistent_lb_own_valid with "tbe1 tbe2") as "%Htb2".
    apply top_bot_state_le in Htb2 as [Hlt21 Htb2].
      fr. iIntros ([<- Hlt]). clear Hlt21.
      assert (t2 < b1) as Hlt21...
    iSplit...
    iDestruct "elt1" as (elts1) "[lb1 [%NO|%Hget1]]"...
    iDestruct "elt2" as (elts2) "[lb2 [%NO|%Hget2]]"...
    rewrite Hget1 Hget2.
    iApply (mono_list_lb_lookup with "lb2 lb1").
    - rewrite -lookup_lt_is_Some -Hget2. apply mod_get_is_Some...
    - rewrite -lookup_lt_is_Some -Hget1. apply mod_get_is_Some...
  Qed.

  Lemma dqst_auth_write_bot v γglob era ca l t b :
    dqst_auth γglob era ca l t b -∗
    dqst_auth γglob era ca (mod_set l b v) t b.
  Proof.
    desγ γglob.
    iIntros "Auth".
      iDestruct "Auth" as (γtbeO) "(%HltO & tbO & eltO & museO)".
      iDestruct "eltO" as (elts) "[Elts %Heltslen]".
    unfold dqst_auth. rewrite mod_set_length. fr.
    fr. case_bool_decide; auto. rewrite mod_set_get_ne; auto.
    apply neq_symm, close_mod_neq; lia.
  Qed.

  Lemma dqst_auth_update γglob era ca l t b :
    t < b →
    dqst_auth γglob era ca l t b ==∗
    dqst_auth γglob era ca l (S t) b.
  Proof with extended_auto.
    desγ γglob.
    iIntros (Hlt) "Auth".
      iDestruct "Auth" as (γtbeO) "(%HltO & [tbO tbeO] & eltO & museO)".
      iDestruct "eltO" as (elts) "[Elts %Heltslen]".
    iMod (mono_nat_own_update (top_bot_state (S t) b)
      with "tbO") as "[tbO _]".
    { unfold top_bot_state. do 2 case_bool_decide... }
    iMod (mono_nat_own_update (top_bot_state (S t) b)
      with "tbeO") as "[tbeO _]".
    { unfold top_bot_state. do 2 case_bool_decide... }

    destruct (decide (S t = b)).
    { iModIntro. fr. fr. do 2 case_bool_decide... }
    destruct (mod_get_is_Some l (S t)) as [v Hv]...
    iMod (mono_list_auth_own_update_app [v] with "Elts") as "[Elts _]".
    iModIntro. fr. fr. do 2 case_bool_decide...
    rewrite app_length lookup_app_r; simpl...
    replace (S t - length elts) with 0; simpl... fr.
  Qed.

  Lemma dqst_auth_push γglob era ca l t b :
    S b < t + length l →
    dqst_auth γglob era ca l t b ==∗
    dqst_auth γglob era ca l t (S b).
  Proof with extended_auto.
    desγ γglob.
    iIntros (Hlt) "Auth".
      iDestruct "Auth" as (γtbeO) "(%HltO & [tbO tbeO] & eltO & museO)".
      iDestruct "eltO" as (elts) "[Elts %Heltslen]".
    iMod (mono_nat_own_update (top_bot_state t (S b))
      with "tbO") as "[tbO _]".
    { unfold top_bot_state. do 2 case_bool_decide... }
    iMod (mono_nat_own_update (top_bot_state t (S b))
      with "tbeO") as "[tbeO _]".
    { unfold top_bot_state. do 2 case_bool_decide... }

    case_bool_decide; last first.
    { iModIntro. fr. fr. case_bool_decide... }
    destruct (mod_get_is_Some l t) as [v Hv]...
    iMod (mono_list_auth_own_update_app [v] with "Elts") as "[Elts _]".
    iModIntro. fr. fr. case_bool_decide...
    rewrite app_length lookup_app_r; simpl...
    replace (t - length elts) with 0; simpl... fr.
  Qed.

  Lemma dqst_auth_pop γglob era ca l t b :
    t < b - 1 →
    dqst_auth γglob era ca l t b ==∗
    dqst_auth γglob era ca l t (b - 1).
  Proof with extended_auto.
    desγ γglob.
    iIntros (Hlt) "Auth".
      iDestruct "Auth" as (γtbeO) "(%HltO & [tbO tbeO] & eltO & museO)".
      iDestruct "eltO" as (elts) "[Elts %Heltslen]".
    replace (top_bot_state t b) with (top_bot_state t (b-1)).
      2: unfold top_bot_state; repeat case_bool_decide...
    iModIntro. fr. fr. case_bool_decide...
  Qed.

  Lemma dqst_auth_archive ca' l' γglob era ca l t b :
    length l ≤ length l' →
    circ_slice l t b = circ_slice l' t b →
    ca ↦∗ l -∗
    dqst_auth γglob era ca l t b ==∗
    dqst_archived γglob era ca l t b ∗
    dqst_auth γglob (S era) ca' l' t b.
  Proof with extended_auto.
    desγ γglob.
    iIntros (Hlong Heqs) "Own Auth".
      iDestruct "Auth" as (γtbeO) "(%HltO & [tbO tbeO] & eltO & museO)".
      iDestruct "eltO" as (elts) "[Elts %Heltslen]".
      iDestruct "museO" as (proom museum) "museO".
      iDestruct "museO" as "([%Hproomlen %Hmuslen] & museO)".
      iDestruct "museO" as "(Room & Museum & Archives)".

    (* archive *)
    iMod (array_persist with "Own") as "#PC".
    iDestruct (mono_nat_lb_own_get with "tbO") as "#tb".
    iMod (mono_nat_own_persist with "tbeO") as "#tbe".
    iDestruct (mono_list_lb_own_get with "Elts") as "#eltslb".
    iDestruct (mono_list_lb_own_get with "Room") as "#roomlb".
    iMod (mono_list_auth_own_update_app [(l, t, b)] with "Museum") as "[Museum #muslb]".
    iSplitR.
    { iModIntro. fr. fr. all: fr.
      - case_bool_decide... iRight. destruct Heltslen...
      - rewrite lookup_app_r... replace (era - length proom) with 0...
      - rewrite lookup_app_r... replace (era - length museum) with 0... 
    }

    (* new era *)
    iMod (mono_nat_own_alloc (top_bot_state t b)) as (γtbe') "[tbeO _]".
    iMod (mono_list_auth_own_update_app [(γtbe', ca')] with "Room") as "[Room #rlb]".

    (* frame *)
    iModIntro. fr. fr.
    iSplitL "Elts".
    { fr. case_bool_decide... fr.
      destruct Heltslen as [_ Hget].
      apply (circ_slice_split_eq (S t)) in Heqs as [Heqs _]...
      destruct (circ_slice_singleton l t) as [x [Hx Hsx]]...
      destruct (circ_slice_singleton l' t) as [y [Hy Hsy]]...
      rewrite Hsx Hsy in Heqs. injection Heqs as [= <-].
      rewrite Hy -Hget Hx...
    }
    fr. fr; simpl...
    { rewrite app_length -Hproomlen. simpl... }
    { rewrite app_length -Hmuslen. simpl... }
    fr. all: fr.
    - case_bool_decide... iRight. destruct Heltslen...
    - rewrite lookup_app_l...
      2: rewrite app_length; simpl...
      rewrite lookup_app_r...
      replace (length proom + 0 - length proom) with 0...
    - rewrite lookup_app_r...
      replace (length proom + 0 - length museum) with 0...
  Qed.
End dqst.

Section proof.
  Context `{!heapGS Σ, !dequeG Σ, !circleG Σ} (N : namespace).
  Notation iProp := (iProp Σ).

  Definition deque_inv (γq γpop γera : gname) (γglob : glob_gnames)
  (C top bot : loc) : iProp :=
    ∃ (era : nat) (arr : loc) (l : list val) (t b : nat),
      ⌜1 ≤ t ≤ b ∧ b < t + length l ∧ length l ≠ 0⌝ ∗
      (* abstract states *)
      ( dqst_auth γglob era arr l t b ∗
        own γq (●E (circ_slice l t b)) ∗
        ghost_var γera (1/2) (era, l)
      ) ∗
      (* circular array *)
      ( C ↦{#1/2} (#arr, #(length l)) ∗
        arr ↦∗{#1/2} l
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
    ∃ (γq γpop γera : gname) (γglob : glob_gnames) (C top bot : loc),
      ⌜q = (#C, #top, #bot)%V⌝ ∗
      ⌜γ = encode (γq, γpop, γera, γglob)⌝ ∗
      inv N (deque_inv γq γpop γera γglob C top bot).
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
    ∃ (γq γpop γera : gname) (γglob : glob_gnames) (era : nat)
    (l : list val) (C arr top bot : loc) (b : nat),
      ⌜γ = encode (γq, γpop, γera, γglob)⌝ ∗
      ⌜q = (#C, #top, #bot)%V⌝ ∗
      (* array state *)
      ghost_var γera (1/2) (era, l) ∗
      (* own circle *)
      ( C ↦{#1/2} (#arr, #(length l)) ∗
        arr ↦∗{#1/2} l
      ) ∗
      (* own bottom *)
      ( bot ↦{#1/2} #b ∗
        ghost_var γpop (1/2) false
      ).
  
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
    wp_alloc arr as "[arr↦1 arr↦2]"... wp_pures.
    wp_alloc bot as "[b↦1 b↦2]". wp_alloc top as "t↦".
    wp_alloc A as "[A↦1 A↦2]". wp_pures.

    (* make resources *)
    iMod (own_alloc (●E [] ⋅ ◯E [])) as (γq) "[γq● γq◯]".
      1: apply excl_auth_valid.
    iMod (ghost_var_alloc false) as (γpop) "[γpop1 γpop2]".
    iMod (dqst_auth_alloc arr (replicate n #0)) as (γglob) "Auth"...
    iMod (ghost_var_alloc (0, replicate n #0)) as (γera) "[eraG1 eraG2]".
    iMod (inv_alloc N _ (deque_inv γq γpop γera γglob A top bot)
      with "[A↦1 t↦ b↦1 arr↦1 γq● γpop1 Auth eraG1]") as "Inv".
    { fr. fr. fr. }

    (* apply Φ *)
    iApply "HΦ". iModIntro. iSplitL "Inv"; first fr.
    iSplitL "γq◯"; fr. fr. instantiate (1:=1)...
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
      iDestruct "Own" as (γq γpop γera γglob) "Own".
        iDestruct "Own" as (era l C arr top bot b) "Own".
        iDestruct "Own" as "(%Enc & %Q & eraOwn & [COwn AOwn] & [bOwn popOwn])".
        subst q.
      iDestruct "Is" as (γq' γpop' γera' γglob') "Inv".
        iDestruct "Inv" as (C' top' bot') "Inv".
        iDestruct "Inv" as "(%Q & %Enc' & Inv)".
        injection Q as [= <- <- <-]. encode_agree Enc.
    wp_lam. unfold code.arr, code.top, code.bot, circ_access. wp_pures.
    wp_load. wp_pures.

    (* 1. load top *)
    wp_bind (! _)%E.
      iInv "Inv" as (era1 arr1 l1 t1 b1) "Invs".
        iDestruct "Invs" as "(>%Htb1 & >Abst & >A & >Top & >Bot)".
      iDestruct "A" as "[C↦ arr↦]".
        iDestruct (mapsto_agree with "COwn C↦") as "%Hl1". injection Hl1 as [= <- Hlen].
        iDestruct (array_agree with "AOwn arr↦") as "%"... subst l1. clear Hlen.
      iCombine "C↦ arr↦" as "A".
      iDestruct "Bot" as (Pop1) "[bot↦ pop]".
        iDestruct (ghost_var_agree with "popOwn pop") as "%". subst Pop1.
        iDestruct (mapsto_agree with "bOwn bot↦") as "%Hb".
        injection Hb as [= Hb]. assert (b = b1)... subst b1. clear Hb.
      iCombine "bot↦ pop" as "Bot".
      iDestruct "Abst" as "(Glob & ● & Era)".
        iDestruct (dqst_get_frag with "Glob") as "#F1".
      iCombine "Glob ● Era" as "Abst".
      wp_load.
      iModIntro. iSplitL "Abst A Top Bot".
      { iExists _,_,l. fr. fr. instantiate (1:=false)... }
    wp_pures. wp_load. wp_pures.
    
    case_bool_decide; last first; wp_pures.
    - (* 2. write to circle *)
      wp_bind (_ <- _)%E.
        iInv "Inv" as (era2 arr2 l2 t2 b2) "Invs".
          iDestruct "Invs" as "(>%Htb2 & >Abst & >A & >Top & >Bot)".
        iDestruct "A" as "[C↦ arr↦]".
          iDestruct (mapsto_agree with "COwn C↦") as "%Hl2". injection Hl2 as [= <- Hlen].
          iDestruct (array_agree with "AOwn arr↦") as "%"... subst l2. clear Hlen.
          iCombine "AOwn arr↦" as "arr↦".
          rewrite rem_mod_eq...
          iApply (wp_store_offset with "[arr↦]")... 1: apply mod_get_is_Some...
          iNext. iIntros "arr↦".
          iDestruct "arr↦" as "[AOwn arr↦]".
        iCombine "C↦ arr↦" as "A".
        iDestruct "Bot" as (Pop2) "[bot↦ pop]".
          iDestruct (ghost_var_agree with "popOwn pop") as "%". subst Pop2.
          iDestruct (mapsto_agree with "bOwn bot↦") as "%Hb".
          injection Hb as [= Hb]. assert (b = b2)... subst b2.
        iCombine "bot↦ pop" as "Bot".
        iDestruct "Abst" as "(Glob & ● & Era)".
          iDestruct (dqst_auth_write_bot v with "Glob") as "Glob"...
          iDestruct (ghost_var_agree with "eraOwn Era") as "%Hera2".
          injection Hera2 as [= <-].
          iMod (ghost_var_update_2 (era, mod_set l b v) with "eraOwn Era") as "[eraOwn Era]"...
        iCombine "Glob ● Era" as "Abst".
      iModIntro. iSplitL "Abst A Top Bot".
      { iExists _,_,(mod_set l b v),t2,b.
        rewrite mod_set_length circ_slice_update_right...
        fr. iExists false... }
      wp_pures.

      (* 3. increment bot *)
      iInv "Inv" as (era3 arr3 l3 t3 b3) "Invs".
        iDestruct "Invs" as "(>%Htb4 & >Abst & A & >Top & >Bot)".
        iDestruct "Bot" as (Pop3) "[bot↦ pop]".
          iDestruct (ghost_var_agree with "pop popOwn") as "%Eq". subst Pop3.
          iDestruct (mapsto_agree with "bOwn bot↦") as "%Eq".
            injection Eq as [= Hb3]. assert (b = b3)... subst b3. clear Hb3.
          iCombine "bOwn bot↦" as "bot↦".
            wp_store. replace (Z.of_nat b + 1)%Z with (Z.of_nat (S b))...
          iDestruct "bot↦" as "[bOwn bot↦]".
        iCombine "bot↦ pop" as "Bot".
        iDestruct "Abst" as "(Glob & ● & Era)".
          iDestruct (dqst_get_lb with "Glob F1") as "%Ht14".
          iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq".
          injection Eq as [= <- <-].
        iCombine "Glob ● Era" as "Abst".
        iDestruct "A" as "[C↦ arr↦]".
          iDestruct (mapsto_agree with "COwn C↦") as "%Hl3". injection Hl3 as [= <- Hlen].
          iDestruct (array_agree with "AOwn arr↦") as "%Hl3".
          1: rewrite insert_length...
        iCombine "C↦ arr↦" as "A".
      iMod "AU" as (l') "[Cont [_ Commit]]".
        iDestruct "Cont" as (γq' γpop' γera' γbglob') "[%Enc' ◯]".
          encode_agree Enc.
        iDestruct "Abst" as "(Glob & ● & Era)".
          iMod (dqst_auth_push with "Glob") as "Glob".
            1: rewrite insert_length...
          iDestruct (own_ea_agree with "● ◯") as "%Hl'".
          iMod (own_ea_update (l' ++ [v]) with "● ◯") as "[● ◯]".
        iCombine "Glob ● Era" as "Abst".
      iMod ("Commit" with "[◯]") as "HΦ". 1: fr.
      
      iModIntro.
      iSplitL "A Abst Top Bot".
      { iExists era, arr, (mod_set l b v), t3, (S b). fr.
        rewrite (circ_slice_extend_right _ _ _ v)...
        2: rewrite mod_set_get... subst l'.
        fr. iExists false...
      }
      iApply "HΦ".
        iExists γq, γpop, γera, γglob.
        iExists era, (mod_set l b v), C, arr, top, bot, (S b).
        fr. rewrite insert_length...
    - (* X. grow *)
      wp_bind (grow_circle _ _ _)%E.
      awp_apply (grow_circle_spec with "[eraOwn COwn AOwn]")...
        iInv "Inv" as (eraX arrX lX tX bX) "Invs".
          iDestruct "Invs" as "(>%HtbX & >Abst & >A & >Top & >Bot)".
        iDestruct "Abst" as "(Glob & ● & Era)".
          iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq".
          injection Eq as [= <- <-].
        iCombine "Glob ● Era" as "Abst".
        iDestruct "A" as "[C↦ arr↦]".
          iDestruct (mapsto_agree with "COwn C↦") as "%HlX".
          injection HlX as [= <-].
          iCombine "AOwn arr↦" as "arr↦".
          iAaccIntro with "arr↦".
          { iIntros "arr↦". iDestruct "arr↦" as "[AOwn arr↦]".
            iCombine "C↦ arr↦" as "A".
            iSplitL "Abst A Top Bot". 2: fr. iExists _,_,l. fr. }
      iIntros (arrX lX) "(%HlenX & %Heqs & arrX↦)".
















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
          iDestruct (dqst_get_lb with "Glob F1") as "%Ht1Y".
          apply (circ_slice_split_eq tY) in Heqs as [_ HeqsY]...
          iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq".
          injection Eq as [= <- <- <-].
          iMod (dqst_auth_archive γcontX caX lX with "Own Glob") as "[#Arch Glob]"...
          iMod (ghost_var_update_2 (S era, γcontX, lX)
            with "eraOwn Era") as "[eraOwn Era]"...
        iCombine "Glob Q Era" as "Abst".
      replace (circ_slice l tY b) with (circ_slice lX tY b); last first.

      iSplitL "A Abst Top Bot".
      { iModIntro; iNext. unfold deque_inv.
        iExists γcontX, (S era), caX, lX, tY, b.
        fr. fr. instantiate (1:=false)... }
      iModIntro. wp_pures. wp_load. wp_pures.

      (* 3. write to circle *)
      iRename "OwnX" into "caOwn".
      iRename "ContC" into "ContCpast".
      awp_apply (set_circle_spec with "[] caOwn")...
        iInv "Inv" as (era3 ca3 l3 t3 b3) "Invs".
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
        iDestruct (dqst_auth_write_bot v with "Glob") as "Glob".
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
      iInv "Inv" as (era4 ca4 l4 t4 b4) "Invs".
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
          iDestruct (dqst_get_lb with "Glob F1") as "%Ht14".
          iMod (dqst_auth_push with "Glob") as "Glob".
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
      iDestruct "Own" as (γq γpop γera γglob γcont) "Own".
        iDestruct "Own" as (era ca l A top bot b) "Own".
        iDestruct "Own" as "(%Enc & %Q & eraOwn & AOwn & caOwn & bOwn & popOwn)".
        subst q.
      iDestruct "Is" as (γq' γpop' γera' γglob') "Inv".
        iDestruct "Inv" as (A' top' bot') "Inv".
        iDestruct "Inv" as "(%Q & %Enc' & Inv)".
        injection Q as [= <- <- <-]. encode_agree Enc.
    wp_lam. unfold code.arr, code.top, code.bot. wp_pures.
    wp_load. wp_pures. wp_load. wp_pures.

    (* 1. decrement bot *)
    wp_bind (_ <- _)%E.
      iInv "Inv" as (era1 ca1 l1 t1 b1) "Invs".
        iDestruct "Invs" as "(>%Htb1 & >Abst & A & >Top & >Bot)".
      iDestruct "Abst" as "(Glob & Q & Era)".
        iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq".
        injection Eq as [= <- <- <-].
      iCombine "Glob Q Era" as "Abst".
      iDestruct "A" as "(>A↦ & #IsC1 & ContC)".
        iDestruct (mapsto_agree with "AOwn A↦") as "%". subst ca1.
      iCombine "A↦ IsC1 ContC" as "A".
      iDestruct "Bot" as (Pop1) "[bot↦ pop]".
        iDestruct (ghost_var_agree with "pop popOwn") as "%". subst Pop1.
        iMod (ghost_var_update_2 true with "pop popOwn") as "[pop popOwn]"...
        iDestruct (mapsto_agree with "bot↦ bOwn") as "%Eq".
        injection Eq as [= Eq]. assert (b = b1)... subst b1. clear Eq.
        iCombine "bot↦ bOwn" as "bot↦". wp_store.
          replace (Z.of_nat b - 1)%Z with (Z.of_nat (b - 1))%Z...
        iDestruct "bot↦" as "[bot↦ bOwn]".
      iCombine "bot↦ pop" as "Bot".
    iModIntro. iSplitL "Abst A Top Bot"; fr.
    { fr. instantiate (1:=true)... }
    wp_pures.

    (* 2. load top *)
    wp_bind (! _)%E.
      iInv "Inv" as (era2 ca2 l2 t2 b2) "Invs".
        iDestruct "Invs" as "(>%Htb2 & >Abst & A & >Top & >Bot)".
      iDestruct "Abst" as "(Glob & Q & Era)".
        iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq".
        injection Eq as [= <- <- <-].
      iCombine "Glob Q Era" as "Abst".
      iDestruct "A" as "(>A↦ & #IsC2 & ContC)".
        iDestruct (mapsto_agree with "AOwn A↦") as "%". subst ca2.
      iCombine "A↦ IsC1 ContC" as "A".
      iDestruct "Bot" as (Pop2) "[bot↦ pop]".
        iDestruct (ghost_var_agree with "pop popOwn") as "%". subst Pop2.
        iDestruct (mapsto_agree with "bot↦ bOwn") as "%Eq".
        injection Eq as [= Eq]. assert (b = b2)... subst b2. clear Eq.
      iCombine "bot↦ pop" as "Bot".
      wp_load.
    
    destruct (decide (t2 < b-1)).
    { (* normal case, this point is the commit point *)
      iMod "AU" as (l') "[Cont [_ Commit]]".
        iDestruct "Cont" as (γq' γpop' γera' γglob') "[%Enc' ◯]".
          encode_agree Enc.
        destruct (mod_get_is_Some l (b-1)) as [x Hx]...
        iDestruct "Abst" as "(Glob & Q & Era)".
          iMod (dqst_auth_pop with "Glob") as "Glob"...
          iDestruct (own_ea_agree with "Q ◯") as "%Eq". subst l'.
          iMod (own_ea_update (circ_slice l t2 (b-1)) with "Q ◯") as "[Q ◯]".
        iCombine "Glob Q Era" as "Abst".
        iDestruct "Bot" as "[bot↦ pop]".
          iMod (ghost_var_update_2 false with "pop popOwn") as "[pop popOwn]"...
        iCombine "bot↦ pop" as "Bot".
      iMod ("Commit" $! (circ_slice l t2 (b-1)) (SOMEV x) with "[◯]") as "HΦ".
      { fr. rewrite -circ_slice_extend_right...
        replace (S (b-1)) with b... }
      iModIntro. iSplitL "Abst A Top Bot"; fr.
      { fr. instantiate (1:=false)... }
      wp_pures.

      case_bool_decide... wp_pures.
      (* 3. read circle *)
      awp_apply get_circle_spec...
        iInv "Inv" as (era3 ca3 l3 t3 b3) "Invs".
          iDestruct "Invs" as "(>%Htb3 & >Abst & A & >Top & >Bot)".
        iDestruct "Abst" as "(Glob & Q & Era)".
          iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq".
          injection Eq as [= <- <- <-].
        iCombine "Glob Q Era" as "Abst".
        iDestruct "Bot" as (Pop3) "[bot↦ pop]".
          iDestruct (ghost_var_agree with "pop popOwn") as "%Eq". subst Pop3.
          iDestruct (mapsto_agree with "bOwn bot↦") as "%Eq".
            injection Eq as [= Hb3]. assert (b-1 = b3)... subst b3. clear Hb3.
        iCombine "bot↦ pop" as "Bot".
        iDestruct "A" as "(>A↦ & #IsC3 & >ContC)".
          iDestruct (mapsto_agree with "AOwn A↦") as "%". subst ca3.
          iAaccIntro with "[ContC]".
          { unfold tele_app.
            instantiate (1:= {| tele_arg_head := l;
              tele_arg_tail := {| tele_arg_head := true |}
            |})... }
          { instantiate (1:=()). fr. fr.
            iSplitR... iSplitR... iExists false... }
          simpl. iIntros (v) "[%Hget ContC]".
            rewrite Hx in Hget. injection Hget as [= <-].
        iCombine "A↦ IsC3 ContC" as "A".
      iModIntro. iSplitL "Abst A Top Bot"; fr.
      { iNext. fr. iExists false... }
      wp_pures.

      case_bool_decide... wp_pures.
      iApply "HΦ". iExists _,_,_,_,_. iExists era, ca, l. fr.
    }

    iModIntro. iSplitL "Abst A Top Bot"; fr.
    { fr. instantiate (1:=true)... }
    wp_pures.

    case_bool_decide; wp_pures.
    - (* empty *)
      assert (t2 = b)... subst t2.
      (* 3. roll back bot *)
      wp_bind (_ <- _)%E.
        iInv "Inv" as (era3 ca3 l3 t3 b3) "Invs".
          iDestruct "Invs" as "(>%Htb3 & >Abst & A & >Top & >Bot)".
        iDestruct "Abst" as "(Glob & Q & Era)".
          iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq".
          injection Eq as [= <- <- <-].
        iCombine "Glob Q Era" as "Abst".
        iDestruct "A" as "(>A↦ & #IsC3 & ContC)".
          iDestruct (mapsto_agree with "AOwn A↦") as "%". subst ca3.
        iCombine "A↦ IsC1 ContC" as "A".
        iDestruct "Bot" as (Pop3) "[bot↦ pop]".
          iDestruct (ghost_var_agree with "pop popOwn") as "%". subst Pop3.
          iMod (ghost_var_update_2 false with "pop popOwn") as "[pop popOwn]"...
          iDestruct (mapsto_agree with "bot↦ bOwn") as "%Eq".
          injection Eq as [= Eq]. assert (b = b3)... subst b3. clear Eq.
          iCombine "bot↦ bOwn" as "bot↦". wp_store.
          iDestruct "bot↦" as "[bot↦ bOwn]".
        iCombine "bot↦ pop" as "Bot".
      iMod "AU" as (l') "[Cont [_ Commit]]".
        iMod ("Commit" $! l' NONEV with "[Cont]") as "HΦ"...
      iModIntro. iSplitL "Abst A Top Bot"; fr.
      { fr. instantiate (1:=false)... }
      wp_pures. iApply "HΦ".
      iExists _,_,_,_,_. iExists era,ca,l,A,top,bot,b. fr.
    - (* non-empty *)
      (* 3. read circle *)
      awp_apply get_circle_spec...
        iInv "Inv" as (era3 ca3 l3 t3 b3) "Invs".
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
          iAaccIntro with "[ContC]".
          { unfold tele_app.
            instantiate (1:= {| tele_arg_head := l;
              tele_arg_tail := {| tele_arg_head := true |}
            |})... }
          { instantiate (1:=()). fr. fr.
            iSplitR... iSplitR... iExists true... }
          simpl. iIntros (v) "[%Hget ContC]".
        iCombine "A↦ IsC3 ContC" as "A".
      iModIntro. iSplitL "Abst A Top Bot"; fr.
      { iNext. fr. iExists true... }
      wp_pures.
      
      (* we already did normal case *)
      case_bool_decide... wp_pures.
      
      (* 4. CAS for one-element case *)
      assert (b = S t2)... subst b.
      wp_bind (CmpXchg _ _ _)%E.
        iInv "Inv" as (era4 ca4 l4 t4 b4) "Invs".
          iDestruct "Invs" as "(>%Htb4 & >Abst & A & >Top & >Bot)".
        iDestruct "Abst" as "(Glob & Q & Era)".
          iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq".
          injection Eq as [= <- <- <-].
        iCombine "Glob Q Era" as "Abst".
        iDestruct "A" as "(>A↦ & #IsC4 & ContC)".
          iDestruct (mapsto_agree with "AOwn A↦") as "%". subst ca4.
        iCombine "A↦ IsC1 ContC" as "A".
        iDestruct "Bot" as (Pop4) "[bot↦ pop]".
          iDestruct (ghost_var_agree with "pop popOwn") as "%". subst Pop4.
          iDestruct (mapsto_agree with "bot↦ bOwn") as "%Eq".
          injection Eq as [= Eq]. assert (S t2 = b4)... subst b4. clear Eq.
        iCombine "bot↦ pop" as "Bot".
      destruct (decide (t2 = t4)).
      + (* success *)
        subst t4. wp_cmpxchg_suc.
          replace (Z.of_nat t2 + 1)%Z with (Z.of_nat (S t2))...
        iMod "AU" as (l') "[Cont [_ Commit]]".
          iDestruct "Cont" as (γq' γpop' γera' γglob') "[%Enc' ◯]".
            encode_agree Enc.
          destruct (mod_get_is_Some l (S t2 - 1)) as [x Hx]...
            rewrite Hget in Hx. injection Hx as [= <-].
          iDestruct "Abst" as "(Glob & Q & Era)".
            iMod (dqst_auth_update with "Glob") as "Glob"...
            iDestruct (own_ea_agree with "Q ◯") as "%Eq". subst l'.
            iMod (own_ea_update [] with "Q ◯") as "[Q ◯]".
          iCombine "Glob Q Era" as "Abst".
          iDestruct "Bot" as "[bot↦ pop]".
            iMod (ghost_var_update_2 true with "pop popOwn") as "[pop popOwn]"...
          iCombine "bot↦ pop" as "Bot".
        iMod ("Commit" $! [] (SOMEV v) with "[◯]") as "HΦ".
        { fr. rewrite (circ_slice_extend_right _ _ _ v)...
          1: rewrite circ_slice_nil...
          replace t2 with (S t2 - 1)... }
        iModIntro. iSplitL "Abst A Top Bot".
        { iExists era, ca, l, (S t2), (S t2).
          rewrite circ_slice_nil... fr. iExists true... }
        wp_pures.

        (* 5. roll back bot *)
        wp_bind (_ <- _)%E.
          iInv "Inv" as (era5 ca5 l5 t5 b5) "Invs".
            iDestruct "Invs" as "(>%Htb5 & >Abst & A & >Top & >Bot)".
          iDestruct "Abst" as "(Glob & Q & Era)".
            iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq".
            injection Eq as [= <- <- <-].
          iCombine "Glob Q Era" as "Abst".
          iDestruct "A" as "(>A↦ & #IsC5 & ContC)".
            iDestruct (mapsto_agree with "AOwn A↦") as "%". subst ca5.
          iCombine "A↦ IsC5 ContC" as "A".
          iDestruct "Bot" as (Pop5) "[bot↦ pop]".
            iDestruct (ghost_var_agree with "pop popOwn") as "%". subst Pop5.
            iMod (ghost_var_update_2 false with "pop popOwn") as "[pop popOwn]"...
            iDestruct (mapsto_agree with "bot↦ bOwn") as "%Eq".
            injection Eq as [= Eq]. assert (S t2 = b5)... subst b5. clear Eq.
            iCombine "bot↦ bOwn" as "bot↦". wp_store.
              replace (Z.of_nat t2 + 1)%Z with (Z.of_nat (S t2))%Z...
            iDestruct "bot↦" as "[bot↦ bOwn]".
          iCombine "bot↦ pop" as "Bot".
        iModIntro. iSplitL "Abst A Top Bot"; fr.
        { fr. instantiate (1:=false)... }
        wp_pures. iApply "HΦ".
        iExists _,_,_,_,_. iExists era,ca,l,A,top,bot,(S t2). fr.
      + (* fail *)
        wp_cmpxchg_fail. { intro NO. injection NO... }
        iMod "AU" as (l') "[Cont [_ Commit]]".
        iMod ("Commit" $! l' NONEV with "[Cont]") as "HΦ"...
        iModIntro. iSplitL "Abst A Top Bot"; fr.
        { fr. instantiate (1:=true)... }
        wp_pures.

        (* 5. roll back bot *)
        wp_bind (_ <- _)%E.
          iInv "Inv" as (era5 ca5 l5 t5 b5) "Invs".
            iDestruct "Invs" as "(>%Htb5 & >Abst & A & >Top & >Bot)".
          iDestruct "Abst" as "(Glob & Q & Era)".
            iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq".
            injection Eq as [= <- <- <-].
          iCombine "Glob Q Era" as "Abst".
          iDestruct "A" as "(>A↦ & #IsC5 & ContC)".
            iDestruct (mapsto_agree with "AOwn A↦") as "%". subst ca5.
          iCombine "A↦ IsC5 ContC" as "A".
          iDestruct "Bot" as (Pop5) "[bot↦ pop]".
            iDestruct (ghost_var_agree with "pop popOwn") as "%". subst Pop5.
            iMod (ghost_var_update_2 false with "pop popOwn") as "[pop popOwn]"...
            iDestruct (mapsto_agree with "bot↦ bOwn") as "%Eq".
            injection Eq as [= Eq]. assert (S t2 = b5)... subst b5. clear Eq.
            iCombine "bot↦ bOwn" as "bot↦". wp_store.
              replace (Z.of_nat t2 + 1)%Z with (Z.of_nat (S t2))%Z...
            iDestruct "bot↦" as "[bot↦ bOwn]".
          iCombine "bot↦ pop" as "Bot".
        iModIntro. iSplitL "Abst A Top Bot"; fr.
        { fr. instantiate (1:=false)... }
        wp_pures. iApply "HΦ".
        iExists _,_,_,_,_. iExists era,ca,l,A,top,bot,(S t2). fr.
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
      iDestruct "Is" as (γq γpop γglob A top bot) "Is".
      iDestruct "Is" as "(%Q & %Enc & Inv)".
      subst q.
    wp_lam. unfold code.arr, code.top, code.bot. wp_pures.

    (* 1. load top *)
    wp_bind (! _)%E.
      iInv "Inv" as (era1 ca1 l1 t1 b1) "Invs".
        iDestruct "Invs" as "(>%Htb1 & >Abst & A & >Top & >Bot)".
      iDestruct "Abst" as "(Glob & Q & Era)".
        iDestruct (dqst_get_frag with "Glob") as "#F1".
      iCombine "Glob Q Era" as "Abst".
      wp_load.
    iModIntro. iSplitL "Abst A Top Bot"; fr.
    wp_pures.

    (* 2. load bot *)
    wp_bind (! _)%E.
      iInv "Inv" as (era2 ca2 l2 t2 b2) "Invs".
        iDestruct "Invs" as "(>%Htb2 & >Abst & A & >Top & >Bot)".
      iDestruct "Abst" as "(Glob & Q & Era)".
        iDestruct (dqst_get_frag with "Glob") as "#F2".
        iDestruct (dqst_get_lb with "Glob F1") as "%Lb12".
      iCombine "Glob Q Era" as "Abst".
      iDestruct "Bot" as (Pop2) "[bot↦ Pop]". wp_load.
      iCombine "bot↦ Pop" as "Bot".
    iModIntro. iSplitL "Abst A Top Bot"; fr.
    wp_pures.

    (* 3. load array *)
    wp_alloc arr as "arr↦". wp_pures.
    wp_bind (! _)%E.
      iInv "Inv" as (era3 ca3 l3 t3 b3) "Invs".
        iDestruct "Invs" as "(>%Htb3 & >Abst & A & >Top & >Bot)".
      iDestruct "Abst" as "(Glob & Q & Era)".
        iDestruct (dqst_get_frag with "Glob") as "#F3".
        iDestruct (dqst_get_lb with "Glob F2") as "%Lb23".
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
      iInv "Inv" as (era4 ca4 l4 t4 b4) "Invs".
        iDestruct "Invs" as "(>%Htb4 & >Abst & A & >Top & >Bot)".
      iDestruct "Abst" as "(Glob & Q & Era)".
        iDestruct (dqst_get_frag with "Glob") as "#F4".
        iDestruct (dqst_get_lb with "Glob F3") as "%Lb34".
      iCombine "Glob Q Era" as "Abst".
    destruct (decide (era3 = era4)) as [eqγ|neqγ].
    - (* array was not archived *)
      subst era4.
      iDestruct (dqst_frag_agree with "F3 F4") as "[% %]".
        subst ca4.
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
      iInv "Inv" as (era5 ca5 l5 t5 b5) "Invs".
        iDestruct "Invs" as "(>%Htb5 & >Abst & A & >Top & >Bot)".
        iDestruct "Abst" as "(Glob & Q & Era)".
          iDestruct (dqst_get_frag with "Glob") as "#F5".
          iDestruct (dqst_get_lb with "Glob F4") as "%Lb45".
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
        iDestruct "Cont" as (γq' γpop' γglob') "[%Enc' ◯]".
        encode_agree Enc.
        iDestruct "Abst" as "(Glob & Q & Era)".
          iDestruct (own_ea_agree with "Q ◯") as "%Hlau". subst lau.
          rewrite (circ_slice_shrink_left _ _ _ x)...
          iMod (own_ea_update (circ_slice l5 (S t1) b5)
            with "Q ◯") as "[Q ◯]".
          iMod (dqst_auth_update with "Glob") as "Glob"...
        iCombine "Glob Q Era" as "Abst".
      iMod ("Commit" $! (circ_slice l5 (S t1) b5) (SOMEV x)
        with "[◯]") as "HΦ"; fr.
      iModIntro. iSplitL "Abst A Top Bot"; fr...
      wp_pures. iApply "HΦ"...
    - (* array was archived *)
      iDestruct "Abst" as "(Glob & Q & Era)".
        iDestruct (dqst_get_archived with "Glob F3")
          as (l' t' b') "#Arch"...
      iCombine "Glob Q Era" as "Abst".
        iDestruct (dqst_archived_get_lb with "Arch F3") as "%Ht3'".
        iDestruct (dqst_archived_get_frag with "Arch") as "F'".
        iDestruct (dqst_archived_get_circle with "Arch") as "PC".
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
      iInv "Inv" as (era5 ca5 l5 t5 b5) "Invs".
        iDestruct "Invs" as "(>%Htb5 & >Abst & A & >Top & >Bot)".
        iDestruct "Abst" as "(Glob & Q & Era)".
          iDestruct (dqst_get_frag with "Glob") as "#F5".
          iDestruct (dqst_get_lb with "Glob F4") as "%Lb45".
          iDestruct (dqst_get_lb with "Glob F'") as "%Lb'5".
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
        iDestruct "Cont" as (γq' γpop' γglob') "[%Enc' ◯]".
        encode_agree Enc.
        iDestruct "Abst" as "(Glob & Q & Era)".
          iDestruct (own_ea_agree with "Q ◯") as "%Hlau". subst lau.
          rewrite (circ_slice_shrink_left _ _ _ x)...
          iMod (own_ea_update (circ_slice l5 (S t1) b5)
            with "Q ◯") as "[Q ◯]".
          iMod (dqst_auth_update with "Glob") as "Glob"...
        iCombine "Glob Q Era" as "Abst".
      iMod ("Commit" $! (circ_slice l5 (S t1) b5) (SOMEV x)
        with "[◯]") as "HΦ"; fr.
      iModIntro. iSplitL "Abst A Top Bot"; fr...
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
