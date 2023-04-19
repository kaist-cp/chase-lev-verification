From iris.algebra Require Import list excl_auth mono_nat.
From iris.bi Require Import derived_laws_later.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import invariants ghost_var ghost_map.
From chase_lev Require Import mono_nat atomic.
From iris.heap_lang Require Import proofmode notation.
From iris.prelude Require Import options.
From chase_lev.resizing Require Import helpers spec.

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
        "grow_rec" "arr" "sz" "narr" "nsz" "t" "b'"
      )
      else #().
  
  Definition grow_circle : val :=
    λ: "circle" "t" "b",
      let: "sz" := Snd "circle" in
      let: "nsz" := #2 * "sz" in
      let: "narr" := AllocN "nsz" #0 in
      grow_circle_rec (Fst "circle") "sz" "narr" "nsz" "t" "b" ;;
      ("narr", "nsz").

  Lemma grow_circle_rec_spec (arr arr' : loc)
  (l l' : list val) (n m t b : nat) :
    length l = n → length l' = m →
    0 < n < m →
    t ≤ b < t + n →
    arr' ↦∗ l' -∗
    <<< ∀∀ (_ : ()), arr ↦∗ l >>>
      grow_circle_rec #arr #n #arr' #m #t #b @ ∅
    <<< ∃∃ (l2' : list val),
      ⌜length l2' = m⌝ ∗
      ⌜circ_slice l t b = circ_slice l2' t b⌝ ∗
      ⌜∀ i, b ≤ i < t + length l → mod_get l' i = mod_get l2' i⌝ ∗
      arr ↦∗ l,
      RET #(), arr' ↦∗ l2'
    >>>.
  Proof with extended_auto.
    iIntros "%Hn %Hm %Hlen %Hlt A'" (Φ) "AU".
      iRevert "A' AU". iRevert (b l' Hm Hlt).
    iLöb as "IH". iIntros (b l') "%Hm %Hlt A' AU".
    wp_lam. unfold circ_access. wp_pures.

    case_bool_decide; last first; wp_pures.
    { (* end loop *)
      iMod "AU" as (_) "[Cont [_ Commit]]".
      iMod ("Commit" $! l' with "[Cont]") as "HΦ"; fr.
      1: repeat rewrite circ_slice_nil...
      iApply "HΦ"...
    }
  
    (* read b *)
    destruct b as [|b]...
    replace (Z.of_nat (S b) - 1)%Z with (Z.of_nat b)...
      rewrite rem_mod_eq...
    wp_bind (! _)%E.
      iMod "AU" as (_) "[A [Abort _]]".
      destruct (mod_get_is_Some l b) as [v Hv]...
      wp_apply (wp_load_offset with "A"). 1: rewrite -Hn...
      iIntros "A".
      iMod ("Abort" with "A") as "AU". 1: fr.
    iModIntro. wp_pures.

    (* write b *)
    wp_bind (_ <- _)%E.
      rewrite rem_mod_eq...
      destruct (mod_get_is_Some l' b) as [v' Hv']...
      iApply (wp_store_offset with "A'"). 1: rewrite -Hm...
    iIntros "!> A'". wp_pures.
    
    (* recurse *)
    iApply ("IH" $! b (<[b `mod` m:=v]> l') with "[] [] [A']")...
      1: rewrite insert_length...
    iAuIntro.
    rewrite /atomic_acc /=.
      iMod "AU" as (_) "[Cont AC]".
      iModIntro. iExists (). iFrame "Cont".
      iSplit.
      { iIntros "Cont".
        iDestruct "AC" as "[Abort _]".
        iMod ("Abort" with "Cont") as "AU". fr. }
    iIntros (l2') "(%Hm' & %Heqs & %Hlast & A)".
      iDestruct "AC" as "[_ Commit]".
    iMod ("Commit" $! l2' with "[A]") as "HΦ".
    { iFrame. iPureIntro. repeat split...
      - rewrite (circ_slice_shrink_right _ _ _ v)...
        2: replace (S b - 1) with b...
        rewrite (circ_slice_shrink_right _ _ (S b) v)...
        all: replace (S b - 1) with b...
        + rewrite Heqs...
        + rewrite -Hlast... unfold mod_get.
          rewrite insert_length Hm list_lookup_insert...
          rewrite Hm. apply Nat.mod_upper_bound...
      - intros i Hi. rewrite -Hlast... unfold mod_get.
        rewrite insert_length Hm list_lookup_insert_ne...
        apply close_mod_neq...
    }
    iIntros "!> A'". iApply "HΦ"...
  Qed.

  Lemma grow_circle_spec (arr : loc) (l : list val) (t b : nat) :
    0 < length l →
    t ≤ b < t + length l → ⊢
    <<< ∀∀ (_ : ()), arr ↦∗ l >>>
      grow_circle (#arr, #(length l))%V #t #b @ ∅
    <<< ∃∃ (arr' : loc) (l' : list val),
      ⌜length l < length l'⌝ ∗
      ⌜circ_slice l t b = circ_slice l' t b⌝ ∗
      arr ↦∗ l,
    RET (#arr', #(length l')), arr' ↦∗ l' >>>.
  Proof with extended_auto.
    iIntros "%Hlen %Hlt" (Φ) "AU".
    wp_lam. wp_pures.
    wp_alloc arr' as "A'"... wp_pures.
    replace (Z.to_nat (2 * Z.of_nat (length l))) with (2 * length l)...
    replace (2 * Z.of_nat (length l))%Z with (Z.of_nat (2 * length l))...

    (* make l' *)
    awp_apply (grow_circle_rec_spec with "[A']")...
    unfold atomic_acc.
    iMod "AU" as (_) "[A AC]".
    iModIntro. iExists (). fr. iSplit.
    { iIntros "A". iDestruct "AC" as "[Abort _]".
      iApply ("Abort" with "A").
    }

    iIntros (l2') "(%Hlen' & %Heqs & %Hrest & A)".
      iDestruct "AC" as "[_ Commit]".
      iMod ("Commit" $! arr' l2' with "[A]") as "HΦ"; fr.
    iIntros "!> A'".
    wp_pures. iModIntro.
    replace (length l + (length l + 0)) with (length l2').
    iApply "HΦ". fr.
  Qed.
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
      let: "circle'" := !(arr "deque") in
      let: "sz'" := Snd "circle'" in
      (circ_access (Fst "circle'") "b" "sz'") <- "v" ;;
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
    (* spec *)
    deque_tokG :> inG Σ (excl_authR $ listO valO);
    (* info: era, arrptr, arr, bot, popping *)
    deque_infoG :> ghost_varG Σ (gname * loc * list val * nat * bool);
    (* RA *)
    topbotG :> mono_natG Σ;
    topeltG :> ghost_mapG Σ nat (option val);
    roomG :> ghost_mapG Σ gname (loc * nat)
  }.

Definition dequeΣ : gFunctors :=
  #[ (*invariant *)
    GFunctor (excl_authR $ listO valO);
    ghost_varΣ (gname * loc * list val * nat * bool);
    (* RA *)
    mono_natΣ;
    ghost_mapΣ nat (option val);
    ghost_mapΣ gname (loc * nat)
  ].

Global Instance subG_dequeΣ {Σ} : subG dequeΣ Σ → dequeG Σ.
Proof. solve_inG. Qed.

Section dqst.
  Context `{!heapGS Σ, !dequeG Σ}.
  Notation iProp := (iProp Σ).
  Definition dqst_gnames : Type := gname*gname*gname.

  Definition top_bot_state (t b : nat) : nat :=
    2*t + (if bool_decide (t < b) then 1 else 0).

  Definition dqst_frag (γdqst : dqst_gnames) (γera : gname)
  (arr : loc) (l : list val) (t b : nat) : iProp :=
    let (γ'       , γroom) := γdqst in
    let (γtb, γelt) := γ' in
    ⌜1 ≤ t ≤ b ∧ b < t + length l ∧ length l ≠ 0⌝ ∗
    (* top-bot profile *)
    ( mono_nat_lb_own γtb (top_bot_state t b) ∗
      mono_nat_lb_own γera (top_bot_state t b)
    ) ∗
    (* top element preservation *)
    ( if (bool_decide (t = b)) then True%I else (t ↪[γelt]□ (mod_get l t))%I
    ) ∗
    (* museum of past gnames and circles *)
    γera ↪[γroom]□ (arr, length l).

  Definition dqst_archived (γdqst : dqst_gnames) (γera : gname)
  (arr : loc) (l : list val) (t b : nat) : iProp :=
    mono_nat_auth_own γera 1 (top_bot_state t b) ∗
    dqst_frag γdqst γera arr l t b.

  Definition dqst_auth (γdqst : dqst_gnames) (γera : gname)
  (arr : loc) (l : list val) (t b : nat) : iProp :=
    let (γ'       , γroom) := γdqst in
    let (γtb, γelt) := γ' in
    ⌜1 ≤ t ≤ b ∧ b < t + length l ∧ length l ≠ 0⌝ ∗
    (* top-bot profile *)
    (mono_nat_auth_own γtb 1 (top_bot_state t b) ∗
      mono_nat_auth_own γera 1 (top_bot_state t b)
    ) ∗
    (* top element preservation *)
    ( ∃ (elts : gmap nat (option val)),
      ghost_map_auth γelt 1 elts ∗
      (if (bool_decide (t = b)) then True%I else (t ↪[γelt]□ (mod_get l t))%I) ∗
      ⌜∀ (n : nat), n ≥ t + (if bool_decide (t = b) then 0 else 1) → elts !! n = None⌝
    ) ∗
    (* museum of past gnames and circles *)
    ( ∃ (proom : gmap gname (loc * nat)),
      ⌜γera ∉ dom proom⌝ ∗
      ghost_map_auth γroom 1 (<[γera := (arr, length l)]> proom) ∗
      γera ↪[γroom]□ (arr, length l) ∗
      [∗ map] γ' ↦ cn' ∈ proom, ( ∃ l' t' b',
        dqst_archived γdqst γ' (cn'.1) l' t' b' ∗
        cn'.1 ↦∗ l'
      )
    ).

  (* Timeless & Persistent *)
  Ltac desγ H :=
    destruct H as ((γtb, γelt), γroom).

  Global Instance dqst_frag_timeless γdqst era ca l t b :
    Timeless (dqst_frag γdqst era ca l t b).
  Proof. desγ γdqst. unfold dqst_frag. case_bool_decide; apply _. Qed.

  Global Instance dqst_frag_persistent γdqst era ca l t b :
    Persistent (dqst_frag γdqst era ca l t b).
  Proof. desγ γdqst. unfold dqst_frag. case_bool_decide; apply _. Qed.
  
  Global Instance dqst_archived_timeless γdqst era ca l t b :
    Timeless (dqst_archived γdqst era ca l t b).
  Proof. desγ γdqst. apply _. Qed.

  Global Instance dqst_auth_timeless γdqst era ca l t b :
    Timeless (dqst_auth γdqst era ca l t b).
  Proof. desγ γdqst. unfold dqst_auth. case_bool_decide; apply _. Qed.
  
  Lemma top_bot_state_le t1 b1 t2 b2 :
    top_bot_state t1 b1 ≤ top_bot_state t2 b2 ↔
    t1 ≤ t2 ∧ (t1 = t2 ∧ t1 < b1 → t2 < b2).
  Proof. unfold top_bot_state. do 2 case_bool_decide; lia. Qed.

  Lemma dqst_auth_alloc ca l :
    length l ≠ 0 →
    ⊢ |==> ∃ (γdqst : dqst_gnames) (γ0 : gname),
      dqst_auth γdqst γ0 ca l 1 1.
  Proof.
    intros Hl. unfold dqst_auth.
    iMod (mono_nat_own_alloc 2) as (γtb) "[tb _]".
    iMod (mono_nat_own_alloc 2) as (γera) "[tbe _]".
    iMod (ghost_map_alloc (∅ : gmap nat (option val))) as (γelt) "[topelt _]".
    iMod (ghost_map_alloc ∅) as (γroom) "[room _]".
    iMod (ghost_map_insert γera (ca, length l) with "[room]") as "[room ↪0]". 2: fr. 1: fr.
    iMod (ghost_map_elem_persist with "↪0") as "↪0".
    iExists (γtb, γelt, γroom).
    iModIntro. fr. fr. iSplitL "topelt"; fr.
  Qed.

  Lemma dqst_frag_agree γdqst era ca1 l1 t1 b1 ca2 l2 t2 b2 :
    dqst_frag γdqst era ca1 l1 t1 b1 -∗
    dqst_frag γdqst era ca2 l2 t2 b2 -∗
    ⌜ca1 = ca2 ∧ length l1 = length l2⌝.
  Proof.
    desγ γdqst.
    iIntros "F1 F2".
      iDestruct "F1" as "(%Hlt1 & tb1 & elt1 & muse1)".
      iDestruct "F2" as "(%Hlt2 & tb2 & elt2 & muse2)".
    iDestruct (ghost_map_elem_agree with "muse1 muse2") as "%Eqera".
    injection Eqera; fr.
  Qed.

  Lemma dqst_get_frag γdqst era ca l t b :
    dqst_auth γdqst era ca l t b -∗
    dqst_frag γdqst era ca l t b.
  Proof with extended_auto.
    desγ γdqst.
    iIntros "Auth".
      iDestruct "Auth" as "(%HltO & [tbO tbeO] & eltO & museO)".
      iDestruct "eltO" as (elts) "(Elt & top↪ & %Heltslen)".
      iDestruct "museO" as (room) "(%Hroomlen & Room & era↪ & Archives)".
    iDestruct (mono_nat_lb_own_get with "tbO") as "lb".
    iDestruct (mono_nat_lb_own_get with "tbeO") as "lbe".
    fr.
  Qed.

  Lemma dqst_get_archived γdqst era1 ca1 l1 t1 b1
  era2 ca2 l2 t2 b2 :
    (* era1 is later than era2 *)
    era1 ≠ era2 →
    dqst_auth γdqst era1 ca1 l1 t1 b1 -∗
    dqst_frag γdqst era2 ca2 l2 t2 b2 -∗
    ∃ l' t' b',
      dqst_archived γdqst era2 ca2 l' t' b' ∗
      ca2 ↦∗ l' ∗
      (dqst_archived γdqst era2 ca2 l' t' b' -∗
        ca2 ↦∗ l' -∗
        dqst_auth γdqst era1 ca1 l1 t1 b1).
  Proof with extended_auto.
    desγ γdqst.
    iIntros (Hneq) "Auth F".
      iDestruct "Auth" as "(%HltO & tbO & eltO & museO)".
      iDestruct "museO" as (room) "(%Hroomlen & Room & era↪ & Archives)".
      iDestruct "F" as "(%Hlt & tb & elt & muse)".
    iDestruct (ghost_map_lookup with "Room muse") as "%Hera2".
      assert (room !! era2 = Some (ca2, length l2)).
      1: rewrite lookup_insert_ne in Hera2...
    iDestruct (big_sepM_lookup_acc _ _ era2 with "Archives") as "[Arch Close]"...
      iDestruct "Arch" as (l' t' b') "[Arch2 arr]".
    iExists l'. fr. iIntros "Arch2 arr".
    iSpecialize ("Close" with "[Arch2 arr]"). all: fr.
  Qed.

  Lemma dqst_get_lb γdqst era1 ca1 l1 t1 b1
  era2 ca2 l2 t2 b2 :
    (* era1 is later than era2 *)
    dqst_auth γdqst era1 ca1 l1 t1 b1 -∗
    dqst_frag γdqst era2 ca2 l2 t2 b2 -∗
    ⌜t2 ≤ t1 ∧ (
      (t2 = t1 ∧ t2 < b2) →
      (t1 < b1 ∧ mod_get l2 t2 = mod_get l1 t1)
    )⌝.
  Proof with extended_auto.
    desγ γdqst.
    iIntros "Auth F".
      iDestruct "Auth" as "(%HltO & [tbO tbeO] & eltO & museO)".
      iDestruct "F" as "(%Hlt & [tb tbe] & elt & muse)".
    iDestruct (mono_nat_lb_own_valid with "tbO tb") as "[_ %Htb]".
      apply top_bot_state_le in Htb as [Ht21 Htb21]. fr.
    iIntros ([H1 Ht1b2]). subst t2. assert (t1 < b1) as Htb1... fr.
    iDestruct "eltO" as (elts) "(Elt & top↪ & %Heltslen)". do 2 case_bool_decide...
    iDestruct (ghost_map_elem_agree with "elt top↪") as "%"...
  Qed.

  Lemma dqst_archived_get_frag γdqst era ca l t b :
    dqst_archived γdqst era ca l t b -∗
    dqst_frag γdqst era ca l t b.
  Proof. desγ γdqst. by iIntros "[_ F]". Qed.

  Lemma dqst_archived_get_lb γdqst era ca l1 t1 b1 l2 t2 b2 :
    dqst_archived γdqst era ca l1 t1 b1 -∗
    dqst_frag γdqst era ca l2 t2 b2 -∗
    ⌜t2 ≤ t1 ∧ (
      (t2 = t1 ∧ t2 < b2) →
      (t1 < b1 ∧ mod_get l2 t2 = mod_get l1 t1)
    )⌝.
  Proof with extended_auto.
    desγ γdqst.
    iIntros "Arc F".
      iDestruct "Arc" as "[tbe1 F1]".
      iDestruct "F1" as "(%Hlt1 & [tb1 _] & elt1 & muse1)".
      iDestruct "F" as "(%Hlt2 & [tb2 tbe2] & elt2 & muse2)".
    iDestruct (mono_nat_lb_own_valid with "tbe1 tbe2") as "[_ %Htb2]".
    apply top_bot_state_le in Htb2 as [Hlt21 Htb2].
      fr. iIntros ([<- Hlt]). fr.
    do 2 case_bool_decide...
    iDestruct (ghost_map_elem_agree with "elt2 elt1") as "%"...
  Qed.

  Lemma dqst_auth_write_bot v γdqst era ca l t b :
    dqst_auth γdqst era ca l t b -∗
    dqst_auth γdqst era ca (mod_set l b v) t b.
  Proof.
    desγ γdqst.
    iIntros "Auth".
      iDestruct "Auth" as "(%HltO & tbO & eltO & museO)".
    unfold dqst_auth. rewrite mod_set_length. case_bool_decide; fr.
    rewrite mod_set_get_ne. 1: fr. apply neq_symm, close_mod_neq; lia.
  Qed.

  Lemma dqst_auth_update γdqst era ca l t b :
    t < b →
    dqst_auth γdqst era ca l t b ==∗
    dqst_auth γdqst era ca l (S t) b.
  Proof with extended_auto.
    desγ γdqst.
    iIntros (Hlt) "Auth".
      iDestruct "Auth" as "(%HltO & [tbO tbeO] & eltO & museO)".
      iDestruct "eltO" as (elts) "(Elts & top↪ & %Heltslen)".
      case_bool_decide...
    iMod (mono_nat_own_update (top_bot_state (S t) b) with "tbO") as "[tbO _]".
    { unfold top_bot_state. do 2 case_bool_decide... }
    iMod (mono_nat_own_update (top_bot_state (S t) b) with "tbeO") as "[tbeO _]".
    { unfold top_bot_state. do 2 case_bool_decide... }

    destruct (decide (S t = b)) as [Htb|Htb].
    { iModIntro. fr. fr. case_bool_decide... fr.
      iPureIntro. intros. apply Heltslen... }
    destruct (mod_get_is_Some l (S t)) as [v Hv]...
    iMod (ghost_map_insert (S t) (mod_get l (S t)) with "Elts") as "[Elts topS↪]".
      1: apply Heltslen...
      iMod (ghost_map_elem_persist with "topS↪") as "topS↪".
    iModIntro. fr. fr. case_bool_decide... fr.
    iPureIntro. intros. rewrite lookup_insert_ne... apply Heltslen...
  Qed.

  Lemma dqst_auth_push γdqst era ca l t b :
    S b < t + length l →
    dqst_auth γdqst era ca l t b ==∗
    dqst_auth γdqst era ca l t (S b).
  Proof with extended_auto.
    desγ γdqst.
    iIntros (Hlt) "Auth".
      iDestruct "Auth" as "(%HltO & [tbO tbeO] & eltO & museO)".
      iDestruct "eltO" as (elts) "(Elts & top↪ & %Heltslen)".
    iMod (mono_nat_own_update (top_bot_state t (S b)) with "tbO") as "[tbO _]".
    { unfold top_bot_state. do 2 case_bool_decide... }
    iMod (mono_nat_own_update (top_bot_state t (S b)) with "tbeO") as "[tbeO _]".
    { unfold top_bot_state. do 2 case_bool_decide... }

    case_bool_decide; last first.
    { iModIntro. fr. fr. case_bool_decide... }
    iMod (ghost_map_insert t (mod_get l t) with "[Elts]") as "[Elts ntop↪]"...
      1: apply Heltslen...
      iMod (ghost_map_elem_persist with "ntop↪") as "#ntop↪".
    iModIntro. fr. fr. case_bool_decide... fr.
    iPureIntro. intros m Hm. apply lookup_insert_None. split... apply Heltslen...
  Qed.

  Lemma dqst_auth_pop γdqst era ca l t b :
    t < b - 1 →
    dqst_auth γdqst era ca l t b ==∗
    dqst_auth γdqst era ca l t (b - 1).
  Proof with extended_auto.
    desγ γdqst.
    iIntros (Hlt) "Auth".
      iDestruct "Auth" as "(%HltO & [tbO tbeO] & eltO & museO)".
      iDestruct "eltO" as (elts) "(Elts & top↪ & %Heltslen)".
    replace (top_bot_state t b) with (top_bot_state t (b-1)).
      2: unfold top_bot_state; repeat case_bool_decide...
    iModIntro. fr. fr. case_bool_decide... fr.
  Qed.

  Lemma dqst_auth_archive ca' l' γdqst era ca l t b :
    length l ≤ length l' →
    circ_slice l t b = circ_slice l' t b →
    ca ↦∗ l -∗
    dqst_auth γdqst era ca l t b ==∗
    ∃ (γera' : gname), dqst_auth γdqst γera' ca' l' t b.
  Proof with extended_auto.
    desγ γdqst.
    iIntros (Hlong Heqs) "Own Auth".
      iDestruct "Auth" as "(%HltO & [tbO tbeO] & eltO & museO)".
      iDestruct "eltO" as (elts) "(Elts & top↪ & %Heltslen)".
      iDestruct "museO" as (proom) "(%Hproomlen & Room & era↪ & Archives)".

    (* archive *)
    iDestruct (mono_nat_lb_own_get with "tbO") as "#tbOlb".
    iDestruct (mono_nat_lb_own_get with "tbeO") as "#tbeOlb".

    (* new era *)
    iMod (mono_nat_own_alloc_strong
      (λ γ, γ ∉ (dom (<[era:=(ca, length l)]> proom) ))
      (top_bot_state t b)
    ) as (γera') "[%Hγ' [tbe' _]]".
      1: apply pred_infinite_gname_notin.
    iMod (ghost_map_insert γera' (ca', length l') with "Room") as "[Room era'↪]".
      1: apply not_elem_of_dom...
      iMod (ghost_map_elem_persist with "era'↪") as "#era'↪".

    (* frame *)
    iModIntro. fr. fr. case_bool_decide.
    - iSplitL "Elts"; fr. fr. rewrite big_sepM_insert. 2: apply not_elem_of_dom...
      fr. iExists l, t, b. fr. fr.
    - iDestruct "top↪" as "#top↪".
      iSplitL "Elts top↪"; fr; last first.
      + fr. rewrite big_sepM_insert. 2: apply not_elem_of_dom...
        fr. iExists l, t, b. fr. fr.
      + apply (circ_slice_split_eq (S t)) in Heqs as [Heqs _]...
        destruct (circ_slice_singleton l t) as [x [Hx Hsx]]...
        destruct (circ_slice_singleton l' t) as [y [Hy Hsy]]...
        rewrite Hsx Hsy in Heqs. injection Heqs as [= <-]. rewrite Hy Hx...
  Qed.
End dqst.

Section proof.
  Context `{!heapGS Σ, !dequeG Σ, !circleG Σ} (N : namespace).
  Notation iProp := (iProp Σ).

  Definition deque_inv (γq γsw : gname) (γdqst : dqst_gnames)
  (C top bot : loc) : iProp :=
    ∃ (γera : gname) (arr : loc) (l : list val) (t b : nat) (pop : bool),
      ⌜1 ≤ t ≤ b ∧ b < t + length l ∧ length l ≠ 0⌝ ∗
      (* abstract *)
      own γq (●E (circ_slice l t b)) ∗
      ghost_var γsw (1/2) (γera, arr, l, b, pop) ∗
      dqst_auth γdqst γera arr l t b ∗
      (* physical *)
      C ↦{#1/2} (#arr, #(length l)) ∗
      arr ↦∗{#1/2} l ∗
      top ↦ #t ∗
      bot ↦{#1/2} #(if pop then b-1 else b).

  Definition is_deque (γ : gname) (q : val) : iProp :=
    ∃ (γq γsw : gname) (γdqst : dqst_gnames) (C top bot : loc),
      ⌜q = (#C, #top, #bot)%V⌝ ∗
      ⌜γ = encode (γq, γsw, γdqst)⌝ ∗
      inv N (deque_inv γq γsw γdqst C top bot).
  Global Instance is_deque_persistent γ p :
    Persistent (is_deque γ p) := _.

  Definition deque_content (γ : gname) (frag : list val) : iProp :=
    ∃ (γq γsw : gname) (γdqst : dqst_gnames),
      ⌜γ = encode (γq, γsw, γdqst)⌝ ∗
      own γq (◯E frag).
  Global Instance deque_content_timeless γ frag :
    Timeless (deque_content γ frag) := _.

  (* owner of the deque who can call push and pop *)
  Definition own_deque (γ : gname) (q : val) : iProp :=
    ∃ (γq γsw γera : gname) (γdqst : dqst_gnames)
    (l : list val) (C arr top bot : loc) (b : nat),
      ⌜γ = encode (γq, γsw, γdqst)⌝ ∗
      ⌜q = (#C, #top, #bot)%V⌝ ∗
      ghost_var γsw (1/2) (γera, arr, l, b, false) ∗
      C ↦{#1/2} (#arr, #(length l)) ∗
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
    {{{ γ p, RET p;
      is_deque γ p ∗ deque_content γ [] ∗ own_deque γ p
    }}}.
  Proof with extended_auto.
    iIntros (Hsz Φ) "_ HΦ". wp_lam.

    (* allocate *)
    wp_alloc arr as "[arr↦1 arr↦2]"... wp_pures.
    wp_alloc bot as "[b↦1 b↦2]". wp_alloc top as "t↦".
    wp_alloc C as "[C↦1 C↦2]". wp_pures.

    (* make resources *)
    iMod (own_alloc (●E [] ⋅ ◯E [])) as (γq) "[γq● γq◯]". 1: apply excl_auth_valid.
    iMod (dqst_auth_alloc arr (replicate n #0)) as (γdqst γera) "Auth"...
    iMod (ghost_var_alloc (γera, arr, (replicate n #0), 1, false)) as (γsw) "[Era1 Era2]".
    iMod (inv_alloc N _ (deque_inv γq γsw γdqst C top bot)
      with "[C↦1 t↦ b↦1 arr↦1 γq● Auth Era1]") as "Inv".
    { fr. fr. }

    (* apply Φ *)
    iApply "HΦ". iModIntro. iSplitL "Inv"; first fr.
    iSplitL "γq◯"; fr. fr.
  Qed.

  Lemma push_spec γ p (v : val) :
    is_deque γ p -∗
    own_deque γ p -∗
    <<< ∀∀ l : list val, deque_content γ l >>>
      push p v @ ↑N
    <<< deque_content γ (l ++ [v]),
      RET #(), own_deque γ p >>>.
  Proof with extended_auto.
    iIntros "#Is Own" (Φ) "AU".
      iDestruct "Own" as (γq γsw γera) "Own".
        iDestruct "Own" as (γdqst l C arr top bot b) "Own".
        iDestruct "Own" as "(%Enc & %Q & eraOwn & COwn & AOwn & bOwn)".
        subst p.
      iDestruct "Is" as (γq' γsw' γdqst') "Inv".
        iDestruct "Inv" as (C' top' bot') "Inv".
        iDestruct "Inv" as "(%Q & %Enc' & Inv)".
        injection Q as [= <- <- <-]. encode_agree Enc.
    wp_lam. unfold code.arr, code.top, code.bot, circ_access. wp_pures.
    wp_load. wp_pures.

    (* 1. load top *)
    wp_bind (! _)%E.
      iInv "Inv" as (γera1 arr1 l1 t1 b1 pop1) ">Invs".
        iDestruct "Invs" as "(%Htb1 & ● & Era & Dqst & C & A & T & B)".
      iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <-].
      iDestruct (dqst_get_frag with "Dqst") as "#F1".
      wp_load.
    iModIntro. iSplitL "● Era Dqst C A T B".
    { iExists _,_,l. fr. }
    wp_pures. wp_load. wp_pures.
    
    case_bool_decide; last first; wp_pures.
    - (* 2. write to circle *)
      wp_load. wp_pures. rewrite rem_mod_eq...
      wp_bind (_ <- _)%E.
        iInv "Inv" as (γera2 arr2 l2 t2 b2 pop2) ">Invs".
          iDestruct "Invs" as "(%Htb2 & ● & Era & Dqst & C & A & T & B)".
        iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <-].
        iMod (ghost_var_update_halves (γera, arr, (mod_set l b v), b, false)
          with "eraOwn Era") as "[eraOwn Era]".
        iDestruct (dqst_auth_write_bot v with "Dqst") as "Dqst".
        iCombine "AOwn A" as "A".
          iApply (wp_store_offset with "A"). 1: apply mod_get_is_Some...
        iIntros "!> [AOwn A]".
      iModIntro. iSplitL "● Era Dqst C A T B".
      { iExists _,_,(mod_set l b v),t2,b.
        rewrite mod_set_length circ_slice_update_right... fr. }
      wp_pures.

      (* 3. increment bot *)
      iInv "Inv" as (γera3 arr3 l3 t3 b3 pop3) ">Invs".
        iDestruct "Invs" as "(%Htb3 & ● & Era & Dqst & C & A & T & B)".
        iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <-].
        iMod (ghost_var_update_halves (γera, arr, (mod_set l b v), S b, false)
          with "eraOwn Era") as "[eraOwn Era]".
        iDestruct (dqst_get_lb with "Dqst F1") as "%Ht13".
          iMod (dqst_auth_push with "Dqst") as "Dqst". 1: rewrite mod_set_length...
        iCombine "bOwn B" as "B". wp_store.
          replace (Z.of_nat b + 1)%Z with (Z.of_nat (S b))...
        iDestruct "B" as "[bOwn B]".
      iMod "AU" as (l') "[Cont [_ Commit]]".
        iDestruct "Cont" as (γq' γsw' γbglob') "[%Enc' ◯]". encode_agree Enc.
        iDestruct (own_ea_agree with "● ◯") as "%Hl'".
        iMod (own_ea_update (l' ++ [v]) with "● ◯") as "[● ◯]".
        iMod ("Commit" with "[◯]") as "HΦ". 1: fr.
      iModIntro. iSplitL "● Era Dqst C A T B".
      { iExists γera, arr, (mod_set l b v), t3, (S b). fr.
        rewrite (circ_slice_extend_right _ _ _ v)... 2: rewrite mod_set_get...
        subst l'. fr. rewrite mod_set_length... }
      iApply "HΦ".
        iExists γq, γsw, γera, γdqst.
        iExists (mod_set l b v), C, arr, top, bot, (S b).
        fr. rewrite insert_length...
    - (* X. grow *)
      wp_bind (grow_circle _ _ _)%E.
      awp_apply (grow_circle_spec with "[eraOwn COwn AOwn bOwn AU]")...
        iInv "Inv" as (γeraX arrX lX tX bX popX) ">Invs".
          iDestruct "Invs" as "(%HtbX & ● & Era & Dqst & C & A & T & B)".
        iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <-].
        iCombine "AOwn A" as "A".
          iAaccIntro with "A".
          { iIntros "[AOwn A]". iSplitL "● Era Dqst C A T B". 2: fr.
            iExists _,_,l. fr. }
        iIntros (arrX lX) "(%HlenX & %Heqs & [AOwn A])".
      iModIntro. iSplitL "● Era Dqst C A T B".
      { iExists _,_,l. fr. }
      iIntros "AX". wp_pures.

      (* Y. replace array *)
      wp_bind (_ <- _)%E.
        iInv "Inv" as (γeraY caY lY tY bY popY) ">Invs".
          iDestruct "Invs" as "(%HtbY & ● & Era & Dqst & C & A & T & B)".
        iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <-].
        apply (circ_slice_split_eq tY) in Heqs as Heqsd...
          destruct Heqsd as [_ HeqsR]...
        iCombine "AOwn A" as "A".
          iMod (dqst_auth_archive arrX lX with "[A] [Dqst]") as (γera') "Dqst".
          2: apply HeqsR. all: eauto. 1: fr.
          iDestruct "AX" as "[AOwn A]".
        iMod (ghost_var_update_halves (γera', arrX, lX, b, false)
          with "eraOwn Era") as "[eraOwn Era]".
          iDestruct (dqst_get_lb with "Dqst F1") as "%Ht1Y".
        iCombine "COwn C" as "C". wp_store.
        iDestruct "C" as "[COwn C]".
      iSplitL "● Era Dqst C A T B".
      { iModIntro; iNext. iExists _,_,lX. fr. fr. rewrite -HeqsR... }
      iModIntro. wp_pures. wp_load. wp_pures.

      (* 2. write to circle *)
      rewrite rem_mod_eq...
      wp_bind (_ <- _)%E.
        iInv "Inv" as (γera2 arr2 l2 t2 b2 pop2) ">Invs".
          iDestruct "Invs" as "(%Htb2 & ● & Era & Dqst & C & A & T & B)".
        iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <-].
        iMod (ghost_var_update_halves (γera', arrX, (mod_set lX b v), b, false)
          with "eraOwn Era") as "[eraOwn Era]".
        iDestruct (dqst_auth_write_bot v with "Dqst") as "Dqst".
        iCombine "AOwn A" as "A".
          iApply (wp_store_offset with "A"). 1: apply mod_get_is_Some...
        iIntros "!> [AOwn A]".
      iModIntro. iSplitL "● Era Dqst C A T B".
      { iExists _,_,(mod_set lX b v),t2,b.
        rewrite mod_set_length circ_slice_update_right... fr. }
      wp_pures.

      (* 3. increment bot *)
      iInv "Inv" as (γera3 arr3 l3 t3 b3 pop3) ">Invs".
        iDestruct "Invs" as "(%Htb3 & ● & Era & Dqst & C & A & T & B)".
        iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <-].
        iMod (ghost_var_update_halves (γera', arrX, (mod_set lX b v), S b, false)
          with "eraOwn Era") as "[eraOwn Era]".
        iDestruct (dqst_get_lb with "Dqst F1") as "%Ht13".
          iMod (dqst_auth_push with "Dqst") as "Dqst". 1: rewrite mod_set_length...
        iCombine "bOwn B" as "B". wp_store.
          replace (Z.of_nat b + 1)%Z with (Z.of_nat (S b))...
        iDestruct "B" as "[bOwn B]".
      iMod "AU" as (l') "[Cont [_ Commit]]".
        iDestruct "Cont" as (γq' γsw' γbglob') "[%Enc' ◯]". encode_agree Enc.
        iDestruct (own_ea_agree with "● ◯") as "%Hl'".
        iMod (own_ea_update (l' ++ [v]) with "● ◯") as "[● ◯]".
        iMod ("Commit" with "[◯]") as "HΦ". 1: fr.
      iModIntro. iSplitL "● Era Dqst C A T B".
      { iExists γera', arrX, (mod_set lX b v), t3, (S b), false. fr.
        1: rewrite mod_set_length... subst l'.
        rewrite (circ_slice_extend_right _ _ _ v)... rewrite mod_set_get... }
      iApply "HΦ".
        iExists γq, γsw, γera', γdqst.
        iExists (mod_set lX b v). fr. fr. rewrite insert_length...
    Unshelve. done.
  Qed.

  Lemma pop_spec γ p :
    is_deque γ p -∗
    own_deque γ p -∗
    <<< ∀∀ l : list val, deque_content γ l >>>
      pop p @ ↑N
    <<< ∃∃ (l' : list val) (ov : val),
      deque_content γ l' ∗
      ( ⌜ov = NONEV ∧ l = l'⌝ ∨
        ∃ v, ⌜ov = SOMEV v ∧ l = l' ++ [v]⌝),
      RET ov, own_deque γ p >>>.
  Proof with extended_auto.
    iIntros "#Is Own" (Φ) "AU".
      iDestruct "Own" as (γq γsw γera) "Own".
        iDestruct "Own" as (γdqst l C arr top bot b) "Own".
        iDestruct "Own" as "(%Enc & %Q & eraOwn & COwn & AOwn & bOwn)".
        subst p.
      iDestruct "Is" as (γq' γsw' γdqst') "Inv".
        iDestruct "Inv" as (C' top' bot') "Inv".
        iDestruct "Inv" as "(%Q & %Enc' & Inv)".
        injection Q as [= <- <- <-]. encode_agree Enc.
    wp_lam. unfold code.arr, code.top, code.bot, circ_access. wp_pures.
    wp_load. wp_pures. wp_load. wp_pures.

    (* 1. decrement bot *)
    wp_bind (_ <- _)%E.
      iInv "Inv" as (γera1 ca1 l1 t1 b1 pop1) ">Invs".
        iDestruct "Invs" as "(%Htb1 & ● & Era & Dqst & C & A & T & B)".
      iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <-].
      iMod (ghost_var_update_halves (γera, arr, l, b, true)
        with "eraOwn Era") as "[eraOwn Era]".
      iCombine "bOwn B" as "B". wp_store.
      iDestruct "B" as "[bOwn B]".
    iModIntro. iSplitL "● Era Dqst C A T B".
    { iExists _,_,l. fr. }
    wp_pures.

    (* 2. load top *)
    wp_bind (! _)%E.
      iInv "Inv" as (γera2 ca2 l2 t2 b2 pop2) ">Invs".
        iDestruct "Invs" as "(%Htb2 & ● & Era & Dqst & C & A & T & B)".
      iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <-].
      wp_load.

    destruct (decide (t2 < b-1)) as [Htb|Htb].
    { (* normal case, this point is the commit point *)
      iMod "AU" as (l') "[Cont [_ Commit]]".
        iDestruct "Cont" as (γq' γsw' γdqst') "[%Enc' ◯]". encode_agree Enc.
        destruct (mod_get_is_Some l (b-1)) as [x Hx]...
        iDestruct (own_ea_agree with "● ◯") as "%Eq". subst l'.
        iMod (own_ea_update (circ_slice l t2 (b-1)) with "● ◯") as "[● ◯]".
        iMod (ghost_var_update_halves (γera, arr, l, b-1, false)
          with "eraOwn Era") as "[eraOwn Era]".
        iMod (dqst_auth_pop with "Dqst") as "Dqst"...
      iMod ("Commit" $! (circ_slice l t2 (b-1)) (SOMEV x) with "[◯]") as "HΦ".
      { fr. iRight. fr.
        rewrite -circ_slice_extend_right... replace (S (b-1)) with b... }
      iModIntro. iSplitL "● Era Dqst C A T B".
      { iExists _,_,l,t2. fr. fr. replace (Z.of_nat b - 1)%Z with (Z.of_nat (b - 1))%Z... }
      wp_pures.

      case_bool_decide... wp_pures.
      replace (Z.of_nat b - 1)%Z with (Z.of_nat (b - 1))%Z... rewrite rem_mod_eq...
      wp_bind (! _)%E. iApply (wp_load_offset with "AOwn")...
      iIntros "!> AOwn". wp_pures.
      case_bool_decide... wp_pures.
      iApply "HΦ". iExists _,_,_, _,l. fr.
    }

    iModIntro. iSplitL "● Era Dqst C A T B".
    { iExists _,_,l. fr. }
    wp_pures.

    case_bool_decide; wp_pures.
    { (* empty *)
      assert (t2 = b)... subst t2.
      (* 3. roll back bot *)
      wp_bind (_ <- _)%E.
        iInv "Inv" as (γera3 ca3 l3 t3 b3 pop3) ">Invs".
          iDestruct "Invs" as "(%Htb3 & ● & Era & Dqst & C & A & T & B)".
        iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <-].
        iMod (ghost_var_update_halves (γera, arr, l, b, false)
          with "eraOwn Era") as "[eraOwn Era]".
        iCombine "bOwn B" as "B". wp_store.
        iDestruct "B" as "[bOwn B]".
        iMod "AU" as (l') "[Cont [_ Commit]]".
      iMod ("Commit" $! l' NONEV with "[Cont]") as "HΦ"...
      iModIntro. iSplitL "● Era Dqst C A T B".
      { iExists _,_,l. fr. }
      wp_pures. iApply "HΦ". iExists _,_,_, _,l. fr.
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
      iInv "Inv" as (γera3 ca3 l3 t3 b3 pop3) ">Invs".
        iDestruct "Invs" as "(%Htb3 & ● & Era & Dqst & C & A & T & B)".
      iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <-].
    destruct (decide (t2 = t3)) as [Ht23|Ht23].
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
      iModIntro. iSplitL "● Era Dqst C A T B".
      { iExists γera, arr, l, (S t2), (S t2).
        rewrite circ_slice_nil... fr. fr. }
      wp_pures.

      (* 4. roll back bot *)
      wp_bind (_ <- _)%E.
        iInv "Inv" as (γera4 ca4 l4 t4 b4 pop4) ">Invs".
          iDestruct "Invs" as "(%Htb4 & ● & Era & Dqst & C & A & T & B)".
        iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <-].
        replace (Z.of_nat (S t2 - 1))%Z with (Z.of_nat t2)%Z...
        replace (Z.of_nat (S t2) - 1)%Z with (Z.of_nat t2)%Z...
        iMod (ghost_var_update_halves (γera, arr, l, S t2, false)
          with "eraOwn Era") as "[eraOwn Era]".
        iCombine "bOwn B" as "B". wp_store.
          replace (Z.of_nat t2 + 1)%Z with (Z.of_nat (S t2))%Z...
        iDestruct "B" as "[bOwn B]".
      iModIntro. iSplitL "● Era Dqst C A T B".
      { iExists _,_,l. fr. }
      wp_pures. iApply "HΦ". iExists _,_,_, _,l. fr.
    + (* fail *)
      wp_cmpxchg_fail. { intro NO. injection NO... }
      iMod "AU" as (l') "[Cont [_ Commit]]".
      iMod ("Commit" $! l' NONEV with "[Cont]") as "HΦ"...
      iModIntro. iSplitL "● Era Dqst C A T B".
      { iExists _,_,l. fr. }
      wp_pures.

      (* 4. roll back bot *)
      wp_bind (_ <- _)%E.
        iInv "Inv" as (γera4 ca4 l4 t4 b4 pop4) ">Invs".
          iDestruct "Invs" as "(%Htb4 & ● & Era & Dqst & C & A & T & B)".
        iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <-].
        replace (Z.of_nat (S t2 - 1))%Z with (Z.of_nat t2)%Z...
        replace (Z.of_nat (S t2) - 1)%Z with (Z.of_nat t2)%Z...
        iMod (ghost_var_update_halves (γera, arr, l, S t2, false)
          with "eraOwn Era") as "[eraOwn Era]".
        iCombine "bOwn B" as "B". wp_store.
          replace (Z.of_nat t2 + 1)%Z with (Z.of_nat (S t2))%Z...
        iDestruct "B" as "[bOwn B]".
      iModIntro. iSplitL "● Era Dqst C A T B".
      { iExists _,_,l. fr. }
      wp_pures. iApply "HΦ". iExists _,_,_, _,l. fr.
  Qed.

  Lemma steal_spec γ p :
    is_deque γ p -∗
    <<< ∀∀ l : list val, deque_content γ l >>>
      steal p @ ↑N
    <<< ∃∃ (l' : list val) (ov : val),
      deque_content γ l' ∗
      (⌜ov = NONEV ∧ l = l'⌝ ∨
        ∃ v, ⌜ov = SOMEV v ∧ l = [v] ++ l'⌝),
    RET ov >>>.
  Proof with extended_auto.
    iIntros "#Is" (Φ) "AU".
    iDestruct "Is" as (γq γsw γdqst) "Inv".
      iDestruct "Inv" as (C top bot) "Inv".
      iDestruct "Inv" as "(%Q & %Enc & Inv)".
      subst p.
    wp_lam. unfold code.arr, code.top, code.bot, circ_access. wp_pures.

    (* 1. load top *)
    wp_bind (! _)%E.
      iInv "Inv" as (γera1 ca1 l1 t1 b1 pop1) ">Invs".
        iDestruct "Invs" as "(%Htb1 & ● & Era & Dqst & C & A & T & B)".
      iDestruct (dqst_get_frag with "Dqst") as "#F1".
      wp_load.
    iModIntro. iSplitL "● Era Dqst C A T B".
    { iExists _,_,l1. fr. }
    wp_pures.

    (* 2. load bot *)
    wp_bind (! _)%E.
      iInv "Inv" as (γera2 ca2 l2 t2 b2 pop2) ">Invs".
        iDestruct "Invs" as "(%Htb2 & ● & Era & Dqst & C & A & T & B)".
      iDestruct (dqst_get_frag with "Dqst") as "#F2".
      iDestruct (dqst_get_lb with "Dqst F1") as "%Lb12".
      wp_load.
    iModIntro. iSplitL "● Era Dqst C A T B".
    { iExists _,_,l2. fr. }
    wp_pures.

    (* 3. load array *)
    wp_bind (! _)%E.
      iInv "Inv" as (γera3 ca3 l3 t3 b3 pop3) ">Invs".
        iDestruct "Invs" as "(%Htb3 & ● & Era & Dqst & C & A & T & B)".
      iDestruct (dqst_get_frag with "Dqst") as "#F3".
      iDestruct (dqst_get_lb with "Dqst F2") as "%Lb23".
      wp_load.
    iModIntro. iSplitL "● Era Dqst C A T B".
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
        iDestruct "Invs" as "(%Htb4 & ● & Era & Dqst & C & A & T & B)".
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
      iModIntro. iSplitL "● Era Dqst C A T B".
      { iExists _,_,l4. fr. }
      wp_pures.
      
      (* 5. CAS *)
      wp_bind (CmpXchg _ _ _)%E.
      iInv "Inv" as (γera5 ca5 l5 t5 b5 pop5) ">Invs".
        iDestruct "Invs" as "(%Htb5 & ● & Era & Dqst & C & A & T & B)".
        iDestruct (dqst_get_frag with "Dqst") as "#F5".
        iDestruct (dqst_get_lb with "Dqst F4") as "%Lb45".
      destruct (decide (t1 = t5)); last first.
      { (* fail *)
        wp_cmpxchg_fail. { intro NO. inversion NO... }
        iMod "AU" as (lau) "[Cont [_ Commit]]".
        iMod ("Commit" $! lau NONEV with "[Cont]") as "HΦ"...
        iModIntro. iSplitL "● Era Dqst C A T B".
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
      iModIntro. iSplitL "● Era Dqst C A T B".
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
      iSplitL "● Era Dqst C A T B".
      { iExists _,_,l4. fr. }
      iModIntro. wp_pures.

      (* 5. CAS *)
      wp_bind (CmpXchg _ _ _)%E.
      iInv "Inv" as (γera5 ca5 l5 t5 b5 pop5) ">Invs".
        iDestruct "Invs" as "(%Htb5 & ● & Era & Dqst & C & A & T & B)".
        iDestruct (dqst_get_frag with "Dqst") as "#F5".
        iDestruct (dqst_get_lb with "Dqst F4") as "%Lb45".
      destruct (decide (t1 = t5)); last first.
      { (* fail *)
        wp_cmpxchg_fail. { intro NO. inversion NO... }
        iMod "AU" as (lau) "[Cont [_ Commit]]".
        iMod ("Commit" $! lau NONEV with "[Cont]") as "HΦ"...
        iModIntro. iSplitL "● Era Dqst C A T B".
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
      iModIntro. iSplitL "● Era Dqst C A T B".
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
