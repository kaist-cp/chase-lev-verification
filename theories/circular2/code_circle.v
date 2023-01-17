From iris.algebra Require Import list excl_auth.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import invariants ghost_var mono_nat.
From chase_lev Require Import mono_list atomic.
From iris.heap_lang Require Import proofmode notation.
From iris.prelude Require Import options.
From chase_lev.circular2 Require Import helpers spec_circle.

Section code.
  Definition new_circle : val :=
    λ: "sz",
      let: "array" := AllocN "sz" #0 in
      ("array", "sz").

  Definition size_circle : val :=
    λ: "circle",
      Snd "circle".
  
  Definition get_circle : val :=
    λ: "circle" "i",
      let: "array" := Fst "circle" in
      let: "sz" := Snd "circle" in
      !("array" +ₗ ("i" `rem` "sz")).

  Definition set_circle : val :=
    λ: "circle" "i" "v",
      let: "array" := Fst "circle" in
      let: "sz" := Snd "circle" in
      ("array" +ₗ ("i" `rem` "sz")) <- "v".

  Definition grow_circle_rec : val :=
    rec: "grow_rec" "circle" "ncirc" "t" "b" :=
      if: "t" < "b"
      then (
        let: "b'" := "b" - #1 in
        let: "v" := get_circle "circle" "b'" in
        set_circle "ncirc" "b'" "v" ;;
        "grow_rec" "circle" "ncirc" "t" "b'"
      )
      else #().
  
  Definition grow_circle : val :=
    λ: "circle" "t" "b",
      let: "sz" := Snd "circle" in
      let: "ncirc" := new_circle (#2 * "sz") in
      grow_circle_rec "circle" "ncirc" "t" "b" ;;
      "ncirc".
End code.

(** Ghost state for the circle *)

Class circleG Σ := CircleG {
    circle_tokG :> inG Σ (excl_authR $ listO valO);
  }.

Definition circleΣ : gFunctors :=
  #[GFunctor (excl_authR $ listO valO)
  ].

Global Instance subG_circleΣ {Σ} : subG circleΣ Σ → circleG Σ.
Proof. solve_inG. Qed.

Section proof.
  Context `{!heapGS Σ, !circleG Σ} (N : namespace).
  Notation iProp := (iProp Σ).

  Definition circle_inv (γ : gname) (arr : loc) (n : nat) : iProp :=
    ∃ l,
      ⌜length l = n⌝ ∗
      arr ↦∗{#1/2} l ∗
      own γ (●E l).

  Definition is_circle (γ : gname) (ca : val) : iProp :=
    ∃ (arr : loc) (n : nat),
      ⌜ca = (#arr, #n)%V⌝ ∗
      ⌜n > 0⌝  ∗
      inv N (circle_inv γ arr n).
  Global Instance is_circle_persistent γ q :
    Persistent (is_circle γ q) := _.

  Definition circle_content (γ : gname) (l : list val) : iProp :=
    own γ (◯E l).
  Global Instance circle_content_timeless γ frag :
    Timeless (circle_content γ frag).
  Proof. unfold Timeless, circle_content. iIntros ">C". iFrame. Qed.
    
  Definition persistent_circle (ca : val) (l : list val) : iProp :=
    ∃ (arr : loc),
    ⌜ca = (#arr, #(length l))%V⌝ ∗ arr ↦∗□ l.
  Global Instance persistent_circle_persistent ca l :
    Persistent (persistent_circle ca l) := _.

  Definition own_circle (ca : val) (l : list val) : iProp :=
    ∃ (arr : loc),
      ⌜ca = (#arr, #(length l))%V⌝ ∗
      arr ↦∗{#1/2} l.
  
  Ltac extended_auto :=
    eauto;
    try rewrite replicate_length;
    try rewrite Nat2Z.id;
    try rewrite Qp.half_half;
    try by (
      repeat iNext; repeat iIntros; repeat intros;
      try case_decide; try iPureIntro;
      try rewrite lookup_lt_is_Some;
      try lia; done
    ).
  Ltac fr :=
    repeat iModIntro; repeat iSplit; extended_auto; repeat iExists _;
    iFrame; eauto.

  Lemma circle_content_exclusive γ frag1 frag2 :
    circle_content γ frag1 -∗ circle_content γ frag2 -∗ False.
  Proof.
    iIntros "C1 C2".
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

  Lemma new_circle_spec n :
    0 < n →
    {{{ True }}}
      new_circle #n
    {{{ γ ca l, RET ca;
      ⌜length l = n⌝ ∗
      is_circle γ ca ∗ circle_content γ l ∗ own_circle ca l
    }}}.
  Proof with extended_auto.
    iIntros (Pos Φ) "_ HΦ". wp_lam.
    (* allocate *)
    wp_alloc arr as "[arr↦1 arr↦2]"... wp_pures.
    iMod (own_alloc (●E (replicate n #0) ⋅ ◯E (replicate n #0))) as (γq) "[● ◯]".
      1: apply excl_auth_valid.
    iMod (inv_alloc N _ (circle_inv γq arr n) with "[arr↦2 ●]") as "Inv".
    { iExists (replicate n #0). fr. }
    iApply ("HΦ" $! _ _ (replicate n #0))... fr. fr. fr.
  Qed.

  Lemma size_circle_spec γ ca (i : nat) :
    is_circle γ ca -∗
    <<< ∀∀ (l : list val), circle_content γ l >>>
      size_circle ca @ ↑N
    <<< circle_content γ l, RET #(length l) >>>.
  Proof with extended_auto.
    iIntros "#Is" (Φ) "AU".
      iDestruct "Is" as (arr n) "(-> & %Pos & Inv)".
    wp_lam. wp_pures.
    iInv "Inv" as (l) ">(%Len & arr↦ & ●)".
    iMod "AU" as (l') "[Cont [_ Commit]]".
      iDestruct (own_ea_agree with "● Cont") as "%". subst l'.
    iMod ("Commit" with "Cont") as "Φ".
    iModIntro. iSplitL "● arr↦"; fr. rewrite Len. by iApply "Φ".
  Qed.

  Lemma get_circle_spec γ ca (i : nat) :
    is_circle γ ca -∗
    <<< ∀∀ (l : list val) (current : bool),
      if current then circle_content γ l else persistent_circle ca l >>>
      get_circle ca #i @ ↑N
    <<< ∃∃ v,
      ⌜mod_get l i = Some v⌝ ∗
      if current then circle_content γ l else persistent_circle ca l,
    RET v >>>.
  Proof with extended_auto.
    iIntros "#Is" (Φ) "AU".
      iDestruct "Is" as (arr n) "(-> & %Pos & Inv)".
    wp_lam. wp_pures.

    rewrite rem_mod_eq...
    iInv "Inv" as (l) ">(%Len & arr↦ & ●)".
    iMod "AU" as (l' current) "[Cont [_ Commit]]".
    destruct current.
    - (* is current, has content *)
      iDestruct (own_ea_agree with "● Cont") as "%". subst l'.
      destruct (mod_get_is_Some l i) as [v Hv]...
      iApply (wp_load_offset with "arr↦"). 1: rewrite -Len...
      iNext. iIntros "arr↦".
      iMod ("Commit" $! v with "[Cont]") as "Φ". 1: fr.
      repeat iModIntro.
      iSplitL "● arr↦". { iExists l. fr. }
      by iApply "Φ".
    - (* is past, has persistent array *)
      iDestruct "Cont" as (arr') "[%Heq pers]".
      injection Heq as [= <- Hl']. assert (length l' = n)as Hl'n...
      destruct (mod_get_is_Some l' i) as [v Hv]...
      iApply (wp_load_offset with "pers"). 1: rewrite -Hl'n...
      iNext. iIntros "pers".
      iMod ("Commit" $! v with "[pers]") as "Φ". 1: rewrite -Hl'n; fr.
      repeat iModIntro.
      iSplitL "● arr↦". { iExists l. fr. }
      by iApply "Φ".
  Qed.

  Lemma set_circle_spec γ ca l (i : nat) (v : val) :
    is_circle γ ca -∗ own_circle ca l -∗
    <<< circle_content γ l >>>
      set_circle ca #i v @ ↑N
    <<< circle_content γ (mod_set l i v),
    RET #(), own_circle ca (mod_set l i v) >>>.
  Proof with extended_auto.
    iIntros "#Is Own" (Φ) "AU".
      iDestruct "Is" as (arr n) "(-> & %Pos & Inv)".
    wp_lam. wp_pures.
    
    rewrite rem_mod_eq...
    iInv "Inv" as (l') ">(%Len & arr↦ & ●)".
      iDestruct "Own" as (arr') "[%Eq Own]". injection Eq as [= -> Len'].
      iDestruct (array_agree with "Own arr↦") as "%Heq"... subst l'.
    destruct (mod_get_is_Some l i) as [prv Hprv]...
    iCombine "Own arr↦" as "arr↦".
      iApply (wp_store_offset with "[arr↦]")... 1: rewrite -Len...
      iNext. iIntros "[Own arr↦]".
    iMod "AU" as "[Cont [_ Commit]]".
      iMod (own_ea_update (mod_set l i v) with "● Cont") as "[● Cont]".
    iMod ("Commit" with "Cont") as "Φ".
    iModIntro. iSplitL "● arr↦"; fr; unfold mod_set.
    - rewrite Len; fr. rewrite insert_length...
    - iApply "Φ". fr. rewrite insert_length Len...
  Qed.

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
  Proof with extended_auto.
    iIntros "%Hlen %Hlt #Is Own arr'↦" (Φ) "AU".
      iDestruct "Own" as (arr) "[%Hca arr↦]". subst ca.
      remember (length l') as n eqn:Heqn.
      iRevert "arr'↦ AU". iRevert (b l' Hlt Heqn).
    iLöb as "IH".
      iIntros (b l') "%Hlt %Heqn arr'↦ AU".
    wp_lam. wp_pures.

    case_bool_decide; last first; wp_pures.
    { (* end loop *)
      iMod "AU" as (_) "[Cont [_ Commit]]".
      iMod ("Commit" $! l' with "[Cont] [arr↦ arr'↦]") as "HΦ"; fr.
      2: fr. repeat rewrite circ_slice_to_nil...
    }
  
    (* read b' *)
    destruct b as [|b]...
    replace (Z.of_nat (S b) - 1)%Z with (Z.of_nat b)...
    awp_apply get_circle_spec without "arr↦ arr'↦"...
      rewrite /atomic_acc /=.
      iMod "AU" as (_) "[Cont [Abort _]]".
      iModIntro. iExists l, true. iFrame "Cont".
      iSplit...
      iIntros (v) "[%Hv Cont]".
      iMod ("Abort" with "Cont") as "AU".
    iIntros "!> _ [arr↦ arr'↦]". wp_pures.

    (* write t *)
    unfold set_circle. wp_pures.
    wp_bind (_ <- _)%E.
      rewrite rem_mod_eq...
      iApply (wp_store_offset with "arr'↦"). 
      { rewrite Heqn. apply mod_get_is_Some... }
    iIntros "!> arr'↦". wp_pures.
    
    (* recurse *)
    iSpecialize ("IH" with "arr↦").
    iApply ("IH" $! b (mod_set l' b v) with "[] [] [arr'↦]")...
    1: rewrite insert_length... 1: rewrite Heqn...
    iAuIntro.
    rewrite /atomic_acc /=.
      iMod "AU" as (_) "[Cont AC]".
      iModIntro. iExists (). iFrame "Cont".
      iSplit.
      { iIntros "Cont".
        iDestruct "AC" as "[Abort _]".
        iMod ("Abort" with "Cont") as "AU". fr. }
    iIntros (l2') "(%Hn2' & %Heqs & %Hlast & Cont)".
      iDestruct "AC" as "[_ Commit]".
      iSpecialize ("Commit" $! l2').
    iMod ("Commit" with "[Cont]") as "HΦ".
    { iFrame. iPureIntro. repeat split...
      - rewrite (circ_slice_shrink_right _ _ _ v)...
        2: replace (S b - 1) with b...
        rewrite (circ_slice_shrink_right _ _ (S b) v)...
        all: replace (S b - 1) with b...
        + rewrite Heqs...
        + rewrite -Hlast... unfold mod_get, mod_set.
          rewrite insert_length list_lookup_insert...
          apply Nat.mod_upper_bound...
      - intros i Hi. rewrite -Hlast...
        rewrite mod_set_get_ne...
        apply close_mod_neq...
    }
    iIntros "!> [Own arr'↦]". iApply "HΦ". fr.
  Qed.

  Lemma grow_circle_spec γ ca l (t b : nat) :
    0 < length l →
    t ≤ b < t + length l →
    is_circle γ ca -∗ own_circle ca l -∗
    <<< ∀∀ (_ : ()), circle_content γ l >>>
      grow_circle ca #t #b @ ↑N
    <<< ∃∃ (γ' : gname) (ca' : val) (l' : list val),
      ⌜length l < length l'⌝ ∗
      ⌜circ_slice l t b = circ_slice l' t b⌝ ∗
      is_circle γ' ca' ∗ circle_content γ' l',
    RET ca', own_circle ca l ∗ own_circle ca' l' >>>.
  Proof with extended_auto.
    iIntros "%Hlen %Hlt #Is Own" (Φ) "AU".
      iDestruct "Is" as (arr n) "(%Eq & %Hgt & #Inv)". subst ca.
      iDestruct "Own" as (arr2) "[%Eq Own]".
      injection Eq as [= <- Hn].
    wp_lam. wp_pures.
    unfold new_circle. wp_pures.
    wp_alloc arr' as "arr'↦"... wp_pures.

    (* make l' *)
    replace (Z.to_nat (2 * length l)) with (2 * length l)...
    remember (replicate (2 * length l) #0) as l'.
    replace (2 * Z.of_nat n)%Z with (Z.of_nat (length l'))%Z...
      2: subst l'...

    awp_apply (grow_circle_rec_spec γ (#arr, #n) l arr' l' t b
    with "[] [Own] [arr'↦]")...
      all: try by subst l'; fr. 1: fr; rewrite Hn...
      rewrite /atomic_acc /=.
    iMod "AU" as (_) "[Cont AC]".
      (*iSpecialize ("Commit" $! γq (#arr', #(length l'))%V l).*)
    iModIntro. iExists (). fr. iSplit.
    { iIntros "Cont". iDestruct "AC" as "[Abort _]".
      iApply ("Abort" with "Cont").
    }

    iIntros (l2') "(%Hlen' & %Heqs & %Hrest & Cont)".
      iDestruct "AC" as "[Abort _]".
      iMod ("Abort" with "Cont") as "AU".
    iIntros "!> [Own [arr'↦1 arr'↦2]]".
    wp_pures.

    iMod (own_alloc (●E l2' ⋅ ◯E l2')) as (γ') "[● ◯]".
      1: apply excl_auth_valid.
    iMod (inv_alloc N _ (circle_inv γ' arr' (2*n)) with "[arr'↦2 ●]") as "#Inv'".
    { iExists l2'. fr. rewrite -Hlen' Heql'... }
    iMod "AU" as (_) "[Cont [_ Commit]]".
      iMod ("Commit" $! γ' (#arr', #(length l'))%V l2' with "[◯]") as "HΦ".
      { rewrite -Hlen' Heql'. fr. fr. replace (2*length l) with (2*n)... }
    iApply "HΦ". fr. fr. rewrite -Hlen'...
  Qed.
End proof.

(*
Program Definition atomic_circle `{!heapGS Σ, !circleG Σ} :
  spec_circle.atomic_circle Σ :=
  {| spec_circle.new_circle_spec := new_circle_spec;
     spec_circle.get_circle_spec := get_circle_spec;
     spec_circle.circle_content_exclusive := circle_content_exclusive;
     spec_circle.circle_content_timeless := circle_content_timeless;
     spec_circle_persistent_circle_persistent :=
       persistent_circle_persistent |}.

Global Typeclasses Opaque circle_content is_circle.
*)
