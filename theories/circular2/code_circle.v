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

  Definition grow_circle : val :=
    λ: "circle" "t" "b",
      #().
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

  Definition own_circle (ca : val) : iProp :=
    ∃ (arr : loc) (l : list val),
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
      is_circle γ ca ∗ circle_content γ l ∗ own_circle ca
    }}}.
  Proof with extended_auto.
    iIntros (Pos Φ) "_ HΦ". wp_lam.
    (* allocate *)
    wp_alloc arr as "[arr↦1 arr↦2]"... wp_pures.
    iMod (own_alloc (●E (replicate n #0) ⋅ ◯E (replicate n #0))) as (γq) "[● ◯]".
      1: apply excl_auth_valid.
    iMod (inv_alloc N _ (circle_inv γq arr n) with "[arr↦2 ●]") as "Inv".
    { iExists (replicate n #0). fr. }
    iApply ("HΦ" $! _ _ (replicate n #0))... fr.
    iExists _, (replicate n #0). fr.
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

  Lemma set_circle_spec γ ca (i : nat) (v : val) :
    is_circle γ ca -∗ own_circle ca -∗
    <<< ∀∀ (l : list val), circle_content γ l >>>
      set_circle ca #i v @ ↑N
    <<< circle_content γ (<[i `mod` (length l) := v]> l), RET #() >>>.
  Proof with extended_auto.
    iIntros "#Is Own" (Φ) "AU".
      iDestruct "Is" as (arr n) "(-> & %Pos & Inv)".
    wp_lam. wp_pures.
    
    rewrite rem_mod_eq...
    iInv "Inv" as (l) ">(%Len & arr↦ & ●)".
      iDestruct "Own" as (arr' l') "[%Eq Own]". injection Eq as [= -> Len'].
      iDestruct (array_agree with "Own arr↦") as "%Heq"... subst l'.
    destruct (mod_get_is_Some l i) as [zz Hzz]...
    iCombine "Own arr↦" as "arr↦".
      iApply (wp_store_offset with "[arr↦]")... 1: rewrite -Len...
      iNext. iIntros "[Own arr↦]".
    iMod "AU" as (l') "[Cont [_ Commit]]".
      iDestruct (own_ea_agree with "● Cont") as "%". subst l'.
      iMod (own_ea_update (<[i `mod` (length l) := v]> l) with "● Cont") as "[● Cont]".
    iMod ("Commit" with "Cont") as "Φ".
    iModIntro. iSplitL "● arr↦"; fr.
    - rewrite Len; fr. rewrite insert_length...
    - by iApply "Φ".
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
