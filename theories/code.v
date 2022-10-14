From iris.algebra Require Import excl auth list.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import invariants ghost_var mono_nat.
From chase_lev Require Import atomic.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import proofmode notation.
From iris.prelude Require Import options.
From chase_lev Require Import helpers mono_list.

Definition CAP_CONST : nat := 10.

(*
  We use a finite length list without resizing;
  The push function diverges if bot gets out of bound.
  +--+--+--+--+--+--+--+--
  |99|10|20|30|40|  |  |   ..
  +--+--+--+--+--+--+--+--
      ^           ^
      |           |
      top         bot
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

  Definition definite t b := t + (if decide (t < b) then 1 else 0).

  Definition mono_deque_auth_own (γm : gname) (l : list val) (t b : nat) : iProp :=
    ∃ (γl γtb : gname),
    ⌜γm = encode (γl, γtb)⌝ ∗
    ⌜1 ≤ t ≤ b ≤ CAP_CONST ∧ length l = CAP_CONST⌝ ∗
    mono_list_auth_own γl 1 (take (definite t b) l) ∗
    mono_nat_auth_own γtb 1 (t + definite t b).

  Definition mono_deque_lb_own (γm : gname) (l : list val) (t b : nat) : iProp :=
    ∃ (γl γtb : gname),
    ⌜γm = encode (γl, γtb)⌝ ∗
    ⌜1 ≤ t ≤ b ≤ CAP_CONST ∧ length l = CAP_CONST⌝ ∗
    mono_list_lb_own γl (take (definite t b) l) ∗
    mono_nat_lb_own γtb (t + definite t b).

  Lemma mono_deque_own_alloc l :
    ⌜length l = CAP_CONST⌝ ==∗ ∃ γ, mono_deque_auth_own γ l 1 1.
  Proof.
    iIntros (H).
    iMod (mono_list_own_alloc (take 1 l)) as (γl) "[L _]".
    iMod (mono_nat_own_alloc 2) as (γtb) "[N _]".
    iExists (encode (γl, γtb)). iModIntro.
    iExists _,_. iSplit; iFrame; auto.
    iPureIntro. unfold CAP_CONST. split; auto. lia.
  Qed.

  Lemma mono_deque_get_lb γm l t b :
    mono_deque_auth_own γm l t b -∗
    mono_deque_lb_own γm l t b.
  Proof.
    iIntros "(%γl & %γtb & %ENC & %BOUND & L & N)".
    iDestruct (mono_list_lb_own_get with "L") as "#Llb".
    iDestruct (mono_nat_lb_own_get with "N") as "#Nlb".
    iExists _,_. repeat iSplit; auto. all: iPureIntro; lia.
  Qed.

  Lemma mono_deque_auth_lb_length γm l1 t1 b1 l2 t2 b2 :
    mono_deque_auth_own γm l1 t1 b1 -∗ mono_deque_lb_own γm l2 t2 b2 -∗
    ⌜definite t2 b2 ≤ definite t1 b1⌝.
  Proof.
    iIntros "(%γl & %γtb & %ENC & %BOUND & L & N)".
    iIntros "(%γl' & %γtb' & %ENC' & %BOUND' & L' & N')".
      rewrite ENC in ENC'. apply (inj encode) in ENC'.
      injection ENC' as [= <- <-].
    iDestruct (mono_list_auth_lb_valid with "L L'") as "[_ %Pref]".
    apply prefix_length in Pref. do 2 rewrite take_length in Pref.
    unfold definite in *. do 2 case_decide; iPureIntro; lia.
  Qed.

  Lemma mono_deque_auth_lb_top γm l1 t1 b1 l2 t2 b2 :
    mono_deque_auth_own γm l1 t1 b1 -∗ mono_deque_lb_own γm l2 t2 b2 -∗
    ⌜t2 ≤ t1⌝.
  Proof.
    iIntros "D1 D2".
    iDestruct (mono_deque_auth_lb_length with "D1 D2") as "%D".
    iDestruct "D1" as "(%γl & %γtb & %ENC & %BOUND & L & N)".
    iDestruct "D2" as "(%γl' & %γtb' & %ENC' & %BOUND' & L' & N')".
      rewrite ENC in ENC'. apply (inj encode) in ENC'.
      injection ENC' as [= <- <-].
    iDestruct (mono_nat_lb_own_valid with "N N'") as "[_ %Le]".
    unfold definite in *. do 2 case_decide; iPureIntro; lia.
  Qed.

  Lemma mono_deque_auth_lb_lookup γm i v l1 t1 b1 l2 t2 b2 :
    i < (definite t2 b2) → l2 !! i = Some v →
    mono_deque_auth_own γm l1 t1 b1 -∗ mono_deque_lb_own γm l2 t2 b2 -∗
    ⌜l1 !! i = Some v⌝.
  Proof.
    iIntros (Hi Hv) "D1 D2".
    iDestruct (mono_deque_auth_lb_length with "D1 D2") as "%D".
    iDestruct "D1" as "(%γl & %γtb & %ENC & %BOUND & L & N)".
    iDestruct "D2" as "(%γl' & %γtb' & %ENC' & %BOUND' & L' & N')".
      rewrite ENC in ENC'. apply (inj encode) in ENC'.
      injection ENC' as [= <- <-].
    iDestruct (mono_list_auth_lb_valid with "L L'") as "[_ %Pref]".
    rewrite <- (lookup_take _ (definite t1 b1)) by lia.
    rewrite <- (lookup_take _ (definite t2 b2)) in Hv; auto.
    iPureIntro. by eapply prefix_lookup.
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

  Lemma mono_deque_top_nonempty γm t l1 b1 l2 b2 :
    t < b2 →
    mono_deque_auth_own γm l1 t b1 -∗ mono_deque_lb_own γm l2 t b2 -∗
    ⌜t < b1⌝.
  Proof.
    iIntros (H) "(%γl & %γtb & %ENC & %BOUND & L & N)".
    iIntros "(%γl' & %γtb' & %ENC' & %BOUND' & L' & N')".
      rewrite ENC in ENC'. apply (inj encode) in ENC'.
      injection ENC' as [= <- <-].
    iDestruct (mono_nat_lb_own_valid with "N N'") as "[_ %Le]".
    unfold definite in *. do 2 case_decide; try lia; auto.
  Qed.

  Lemma mono_deque_update_top γm t2 l t1 b :
    t1 ≤ t2 ≤ b →
    mono_deque_auth_own γm l t1 b ==∗ mono_deque_auth_own γm l t2 b.
  Proof.
    iIntros (H) "(%γl & %γtb & %ENC & %BOUND & L & N)".
    iMod (mono_list_auth_own_update (take (definite t2 b) l) with "L") as "[L _]".
      { apply prefix_take. unfold definite. do 2 case_decide; lia. }
    iMod (mono_nat_own_update (t2 + definite t2 b) with "N") as "[N _]".
      { destruct (decide (t1 = t2)); subst; try lia.
        unfold definite. do 2 case_decide; lia. }
    iModIntro.
    iExists _,_. repeat iSplit; auto; iFrame.
    all: iPureIntro; try lia.
  Qed.

  Lemma mono_deque_update_bot γm b2 l t b1 :
    b1 ≤ b2 ≤ CAP_CONST ∨ t < b2 ≤ CAP_CONST →
    mono_deque_auth_own γm l t b1 ==∗ mono_deque_auth_own γm l t b2.
  Proof.
    iIntros (H) "(%γl & %γtb & %ENC & %BOUND & L & N)".
    iMod (mono_list_auth_own_update (take (definite t b2) l) with "L") as "[L _]".
      { apply prefix_take. unfold definite. do 2 case_decide; lia. }
    iMod (mono_nat_own_update (t + definite t b2) with "N") as "[N _]".
      { unfold definite. do 2 case_decide; lia. }
    iModIntro.
    iExists _,_. repeat iSplit; auto; iFrame.
    all: iPureIntro; try lia.
  Qed.
End RA.

Section proof.
  Context `{!heapGS Σ, !dequeG Σ} (N : namespace).
  Notation iProp := (iProp Σ).

  (* TODO: change l to ↦∗{#1} & make another ghost_var in deque_content?
     (see msqueue) *)
  Definition deque_inv (γq γpop γm : gname) (arr top bot : loc) : iProp :=
    ∃ (t b : nat) (l : list val) (Popping : bool),
      let bp := if Popping then b-1 else b in
      ⌜1 ≤ t ≤ b ≤ CAP_CONST ∧ length l = CAP_CONST⌝ ∗
      top ↦ #t ∗ bot ↦{#1/2} #bp ∗ arr ↦∗{#1/2} l ∗
      ghost_var γq (1/2) (slice l t b) ∗
      ghost_var γpop (1/2) Popping ∗
      mono_deque_auth_own γm l t b.

  Definition is_deque (γq γpop γm : gname) (q : val) : iProp :=
    ∃ (arr top bot : loc),
      ⌜q = (#arr, #top, #bot)%V⌝ ∗
      inv N (deque_inv γq γpop γm arr top bot).
  Global Instance is_deque_persistent γq γpop γm q :
    Persistent (is_deque γq γpop γm q) := _.

  Definition deque_content (γq : gname) (frag : list val) : iProp :=
    ghost_var γq (1/2) frag.

  Definition own_deque (γq γpop : gname) (q : val) : iProp :=
    ∃ (arr top bot : loc) (b : nat) (l : list val),
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

  Ltac frameall :=
    repeat iExists _;
    try iFrame "arr↦"; try iFrame "arr↦1"; try iFrame "arr↦2"; 
    iFrame; eauto.
  Ltac autoall :=
    try frameall; eauto;
    unfold CAP_CONST in *; unfold helpers.CAP_CONST in *;
    unfold definite; try case_decide;
    try by (
      repeat iNext; repeat iIntros; repeat intros;
      try iPureIntro;
      try rewrite lookup_lt_is_Some;
      try rewrite Qp.half_half;
      try lia; done
    ).

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
    { iNext... rewrite replicate_length... }
    wp_pures. iModIntro. iApply "HΦ". iSplit...
    iExists _,_,_,1,_...
  Qed.

  Lemma push_spec γq γpop γm q (v : val) :
    is_deque γq γpop γm q -∗
    own_deque γq γpop q -∗
    <<< ∀∀ l : list val, deque_content γq l >>>
      push q v @ ↑N
    <<< deque_content γq (l ++ [v]),
      RET #(), own_deque γq γpop q >>>.
  Proof with autoall.
    iIntros "#Is Own" (Φ) "AU".
      iDestruct "Own" as (arr top bot b l) "(-> & %HL & γ👑 & b👑 & arr👑)".
      iDestruct "Is" as (arr' top' bot') "[%Is Inv]".
      injection Is as [= <- <- <-].
    wp_lam. unfold code.arr, code.bot. wp_pures.

    (* load bot *)
    wp_load. wp_pures.
    case_bool_decide as HbC. { wp_pures. iApply loop_spec... }
    wp_pures.

    (* store value *)
    wp_bind (_ <- _)%E.
    iInv "Inv" as (t1 b1 l1 Pop1)
      ">(%BOUND1 & t↦ & b↦ & arr↦ & γq & γpop & MD)".
      iDestruct (ghost_var_agree with "γ👑 γpop") as "%". subst.
      iDestruct (mapsto_agree with "b↦ b👑") as "%".
        injection H as [=]. apply Nat2Z.inj in H.
      iDestruct (array_agree with "arr↦ arr👑") as "%"... subst.
    iDestruct (mono_deque_auth_insert _ _ _ _ b v with "MD") as "MD"...
    iCombine "arr↦ arr👑" as "arr↦".
      iApply (wp_store_offset with "arr↦")...
      iNext. iIntros "[arr↦ arr👑]". iModIntro.
    iSplitL "t↦ b↦ arr↦ γq γpop MD"...
    { rewrite slice_insert_right... rewrite insert_length... }
    wp_pures.
    replace (Z.of_nat b + 1)%Z with (Z.of_nat (S b))...

    (* store bot *)
    iInv "Inv" as (t2 b2 l2 Pop2)
      ">(%BOUND2 & t↦ & b↦ & arr↦ & γq & γpop & MD)".
      iDestruct (ghost_var_agree with "γ👑 γpop") as "%". subst.
      iDestruct (mapsto_agree with "b↦ b👑") as "%".
        injection H as [=]. apply Nat2Z.inj in H.
      iDestruct (array_agree with "arr↦ arr👑") as "%"; subst.
        1: rewrite insert_length...
    iMod "AU" as (l') "[Cont [_ Commit]]".
      unfold deque_content.
      iDestruct (ghost_var_agree with "γq Cont") as "%"; subst.
      rewrite <- slice_extend_right... 2: rewrite list_lookup_insert...
    iCombine "b↦ b👑" as "b↦". wp_store.
      iDestruct "b↦" as "[b↦ b👑]".
    iMod (ghost_var_update_2 (slice (<[b:=v]> l) t2 (S b))
      with "γq Cont") as "[γq Cont]"...
    iMod (mono_deque_update_bot _ (S b) with "MD") as "MD"...
    iMod ("Commit" with "Cont") as "Φ".
    iModIntro. iModIntro.

    iSplitL "t↦ b↦ arr↦ γq γpop MD"...
    iApply "Φ"... iSplit...
  Qed.

  Lemma pop_spec γq γpop γm q :
    is_deque γq γpop γm q -∗
    own_deque γq γpop q -∗
    <<< ∀∀ l : list val, deque_content γq l >>>
      pop q @ ↑N
    <<< ∃∃ (l' : list val) (b : bool) (v : val),
        deque_content γq l' ∗
        ⌜l = if b then l'++[v] else l'⌝ ,
      RET (#b, v), own_deque γq γpop q >>>.
  Proof with autoall.
    iIntros "#Is Own" (Φ) "AU".
      iDestruct "Own" as (arr top bot b l) "(-> & %HL & γ👑 & b👑 & arr👑)".
      iDestruct "Is" as (arr' top' bot') "[%Is Inv]".
      injection Is as [= <- <- <-].
    wp_lam. unfold code.arr, code.top, code.bot. wp_pures.

    (* load bot *)
    wp_load. wp_pures.

    (* decrement b early *)
    wp_bind (_ <- _)%E.
    iInv "Inv" as (t1 b1 l1 Pop2)
      ">(%BOUND1 & t↦ & b↦ & arr↦ & γq & γpop & MD)".
      iDestruct (ghost_var_agree with "γ👑 γpop") as "%". subst.
      iDestruct (mapsto_agree with "b↦ b👑") as "%".
        injection H as [=]. apply Nat2Z.inj in H.
      iDestruct (array_agree with "arr↦ arr👑") as "%"... subst.
    iCombine "b↦ b👑" as "b↦". wp_store.
      replace (Z.of_nat b-1)%Z with (Z.of_nat (b-1))...
      iDestruct "b↦" as "[b↦ b👑]".
      iMod (ghost_var_update_2 true with "γ👑 γpop") as "[γ👑 γpop]"...
    iModIntro. iSplitL "t↦ b↦ arr↦ γpop γq MD"...
    wp_pures.

    (* load top *)
    wp_bind (! _)%E.
    iInv "Inv" as (t2 b2 l2 Pop1)
      ">(%BOUND2 & t↦ & b↦ & arr↦ & γq & γpop & MD)".
      iDestruct (ghost_var_agree with "γ👑 γpop") as "%". subst.
      iDestruct (mapsto_agree with "b↦ b👑") as "%".
        injection H as [=]. assert (b = b2)... subst. clear H.
      iDestruct (array_agree with "arr↦ arr👑") as "%"... subst.
    (* if t < b-1, this load is the commit point *)
    destruct (decide (t2 < b2-1)).
    { iMod "AU" as (l') "[Cont [_ Commit]]".
        unfold deque_content.
        iDestruct (ghost_var_agree with "Cont γq") as "%". subst.
      assert (is_Some (l !! (b2-1))) as [v Hv]...
        erewrite slice_shrink_right...
      wp_load.
      iMod (ghost_var_update_2 (slice l t2 (b2-1)) with "Cont γq") as "[Cont γq]"...
        iMod (ghost_var_update_2 false with "γ👑 γpop") as "[γ👑 γpop]"...
        iMod (mono_deque_update_bot _ (b2-1) with "MD") as "MD"...
      iMod ("Commit" $! (slice l t2 (b2-1)) true v with "[Cont]") as "Φ"...
      iModIntro. iModIntro. iSplitL "t↦ b↦ arr↦ γq γpop MD"...
      wp_pures. case_bool_decide... wp_pures.
      (* read [b2-1] *)
      wp_bind (! _)%E.
      iApply (wp_load_offset with "arr👑")... iNext. iIntros "arr👑". wp_pures.
      case_bool_decide... wp_pures. iApply "Φ"... }

    (* otherwise... *)
    wp_load. iModIntro. iSplitL "t↦ b↦ arr↦ γpop γq MD"...
    wp_pures.

    (* empty *)
    case_bool_decide as Hbt; wp_pures.
    { wp_bind (_ <- _)%E.
      iInv "Inv" as (t3 b3 l3 Pop4)
        ">(%BOUND3 & t↦ & b↦ & arr↦ & γq & γpop & MD)".
        iDestruct (ghost_var_agree with "γ👑 γpop") as "%". subst.
        iDestruct (mapsto_agree with "b↦ b👑") as "%".
          injection H as [=]. assert (b2 = b3); subst... clear H.
        iDestruct (array_agree with "arr↦ arr👑") as "%"; subst...
      replace t2 with b3...
      (* roll back bot *)
      iCombine "b👑 b↦" as "b↦". wp_store.
        iDestruct "b↦" as "[b👑 b↦]".
        iMod (ghost_var_update_2 false with "γ👑 γpop") as "[γ👑 γpop]"...
      (* AU *)
      iMod "AU" as (l') "[Cont [_ Commit]]".
      iMod ("Commit" $! l' false #() with "[Cont]") as "Φ"...
      iSplitL "t↦ b↦ arr↦ γpop γq MD"...
      iModIntro. wp_pures. iApply "Φ"... }
    
    (* read [b2-1] *)
    wp_bind (! _)%E.
    assert (is_Some (l !! (b2-1))) as [v Hv]...
    iApply (wp_load_offset with "arr👑")... iNext. iIntros "arr👑". wp_pures.

    (* cas top, we already handled normal pop *)
    case_bool_decide... clear H. wp_pures.
    wp_bind (CmpXchg _ _ _)%E.
    iInv "Inv" as (t3 b3 l3 Pop3)
      ">(%BOUND3 & t↦ & b↦ & arr↦ & γq & γpop & MD)".
      iDestruct (ghost_var_agree with "γ👑 γpop") as "%". subst.
      iDestruct (mapsto_agree with "b↦ b👑") as "%".
        injection H as [=]. assert (b2 = b3); subst... clear H.
      iDestruct (array_agree with "arr↦ arr👑") as "%"... subst.
    assert (t2 = b3-1)... subst. clear n Hbt.
    replace (Z.of_nat (b3-1) + 1)%Z with (Z.of_nat b3)...
    destruct (decide (b3-1 = t3)).
    - (* success *)
      subst. wp_cmpxchg_suc.

      (* AU *)
      iMod "AU" as (l') "[Cont [_ Commit]]".
        unfold deque_content.
        iDestruct (ghost_var_agree with "Cont γq") as "%". subst.
      erewrite slice_shrink_left... rewrite slice_to_nil...
      iMod (ghost_var_update_2 [] with "Cont γq") as "[Cont γq]"...
      iMod (mono_deque_update_top _ b3 with "MD") as "MD"...
      iMod ("Commit" $! [] true v with "[Cont]") as "Φ"...
      iModIntro. iSplitL "t↦ b↦ arr↦ γpop γq MD"... 1: rewrite slice_to_nil...
      wp_pures.

      (* store bot *)
      replace (Z.of_nat (b3-1) + 1)%Z with (Z.of_nat b3)...
      wp_bind (_ <- _)%E.
      iInv "Inv" as (t4 b4 l4 Pop4)
        ">(%BOUND4 & t↦ & b↦ & arr↦ & γq & γpop & MD)".
        iDestruct (ghost_var_agree with "γ👑 γpop") as "%". subst.
        iDestruct (mapsto_agree with "b↦ b👑") as "%".
          injection H as [=]. assert (b3 = b4) by lia. subst. clear H.
        iDestruct (array_agree with "arr↦ arr👑") as "%"... subst.
      iCombine "b👑 b↦" as "b↦". wp_store.
        iDestruct "b↦" as "[b👑 b↦]".
      iMod (ghost_var_update_2 false with "γ👑 γpop") as "[γ👑 γpop]"...
      iModIntro. iSplitL "t↦ b↦ arr↦ γpop γq MD"...
      wp_pures. iApply "Φ"...
    - (* fail *)
      wp_cmpxchg_fail. { intro. injection H... }
      iMod "AU" as (l') "[Cont [_ Commit]]".
      iMod ("Commit" $! l' false #() with "[Cont]") as "Φ"...
      iModIntro. iSplitL "t↦ b↦ arr↦ γpop γq MD"...
      wp_pures.

      (* store bot *)
      replace (Z.of_nat (b3-1) + 1)%Z with (Z.of_nat b3)...
      wp_bind (_ <- _)%E.
      iInv "Inv" as (t4 b4 l4 Pop4)
        ">(%BOUND4 & t↦ & b↦ & arr↦ & γq & γpop & MD)".
        iDestruct (ghost_var_agree with "γ👑 γpop") as "%". subst.
        iDestruct (mapsto_agree with "b↦ b👑") as "%".
          injection H as [=]. assert (b3 = b4) by lia. subst. clear H.
        iDestruct (array_agree with "arr↦ arr👑") as "%"... subst.
      iCombine "b👑 b↦" as "b↦". wp_store.
        iDestruct "b↦" as "[b👑 b↦]".
      iMod (ghost_var_update_2 false with "γ👑 γpop") as "[γ👑 γpop]"...
      iModIntro. iSplitL "t↦ b↦ arr↦ γpop γq MD"...
      wp_pures. iApply "Φ"...
  Qed.

  Lemma steal_spec γq γpop γm q :
    is_deque γq γpop γm q -∗
    <<< ∀∀ l : list val, deque_content γq l >>>
      steal q @ ↑N
    <<< ∃∃ (l' : list val) (b : bool) (v : val),
        deque_content γq l' ∗
        ⌜l = if b then [v]++l' else l'⌝ ,
      RET (#b, v) >>>.
  Proof with autoall.
    iIntros "#Is" (Φ) "AU".
      iDestruct "Is" as (arr top bot) "[%Is Inv]". subst.
    wp_lam. unfold code.arr, code.top, code.bot. wp_pures.

    (* load top *)
    wp_bind (! _)%E.
    iInv "Inv" as (t1 b1 l1 Pop1)
      ">(%BOUND1 & t↦ & b↦ & arr↦ & γq & γpop & MD)".
      iDestruct (mono_deque_get_lb with "MD") as "#MDlb1".
    wp_load.
    iModIntro. iSplitL "t↦ b↦ arr↦ γq γpop MD"...
    wp_pures.

    (* load bot *)
    wp_bind (! _)%E.
    iInv "Inv" as (t2 b2 l2 Pop2)
      ">(%BOUND2 & t↦ & b↦ & arr↦ & γq & γpop & MD)".
      iDestruct (mono_deque_get_lb with "MD") as "#MDlb2".
      iDestruct (mono_deque_auth_lb_top with "MD MDlb1") as "%Ht12".
    wp_load.
    iModIntro. iSplitL "t↦ b↦ arr↦ γq γpop MD"...
    wp_pures.

    (* no chance to steal *)
    case_bool_decide; wp_pures.
    { iMod "AU" as (l) "[Cont [_ Commit]]".
      iMod ("Commit" $! l false #() with "[Cont]") as "Φ"...
      iApply "Φ"... }
    assert (t1 < b2) as Htb12. 1: destruct Pop2... clear H.

    (* read [t1] *)
    wp_bind (! _)%E.
    iInv "Inv" as (t3 b3 l3 Pop3)
      ">(%BOUND3 & t↦ & b↦ & arr↦ & γq & γpop & MD)".
      iDestruct (mono_deque_get_lb with "MD") as "#MDlb3".
      iDestruct (mono_deque_auth_lb_top with "MD MDlb2") as "%Ht23".
    assert (is_Some (l3 !! t1)) as [v Hv]...
    iApply (wp_load_offset with "arr↦")... iNext. iIntros "arr↦".
    iModIntro. iSplitL "t↦ b↦ arr↦ γq γpop MD"...
    wp_pures.

    (* cas top *)
    wp_bind (CmpXchg _ _ _)%E.
    iInv "Inv" as (t4 b4 l4 Pop4)
      ">(%BOUND4 & t↦ & b↦ & arr↦ & γq & γpop & MD)".
      iDestruct (mono_deque_auth_lb_top with "MD MDlb3") as "%Ht34".
    destruct (decide (t1 = t4)).
    - (* success *)
      assert (t1 = t2)... assert (t2 = t3)... subst.
      wp_cmpxchg_suc.
      (* update ghost *)
      iDestruct (mono_deque_top_nonempty with "MD MDlb2") as "%Htb34"...
(*
      replace (Z.of_nat t2 + 1)%Z with (Z.of_nat (S t2))...
      iMod (mono_deque_update_top _ (S t2) with "MD") as "MD"...
        iDestruct (mono_deque_get_lb with "MD") as "#MDlb3".
*)
      (* AU *)
      iMod "AU" as (l') "[Cont [_ Commit]]".
        unfold deque_content.
        iDestruct (ghost_var_agree with "γq Cont") as "%". subst.
      iMod (ghost_var_update_2 (slice l3 (S t3) b3) with "γq Cont") as "[γq Cont]"...
      erewrite slice_shrink_left...
      iMod ("Commit" $! (slice l3 (S t2) b3) true v with "[Cont]") as "Φ".
        { iFrame. erewrite slice_shrink_left... }
      iModIntro. iSplitL "t↦ b↦ arr↦ γq γpop MD".
      { iExists _,_,_,_. iFrame "t↦ b↦ arr↦ γq γpop MD"... }
      wp_pures.
      (* load arr[t2] *)
      wp_bind (! _)%E.
      iInv "Inv" as (t4 b4 l4 Pop4)
        ">(%BOUND4 & t↦ & b↦ & arr↦ & γq & γpop & MD)".
        iDestruct (mono_deque_auth_lb with "MD MDlb3") as "[%Ht34 %HL34]".
      assert (l4 !! t2 = Some k).
        { rewrite -(lookup_take _ (S t2))... rewrite -HL34 lookup_take... }
      iApply (wp_load_offset with "arr↦")...
      iNext. iIntros "arr↦".
      iModIntro. iSplitL "t↦ b↦ arr↦ γq γpop MD".
      { iExists _,_,_,_. iFrame "t↦ b↦ arr↦ γq γpop MD"... }
      wp_pures. iApply "Φ"...
    - (* fail *)
      wp_cmpxchg_fail. { intro. injection H... }
      iMod "AU" as (l) "[Cont [_ Commit]]".
      iMod ("Commit" $! l false #() with "[Cont]") as "Φ"...
      iModIntro. iSplitL "t↦ b↦ arr↦ γq γpop MD".
      { iExists _,_,_,_. iFrame "t↦ b↦ arr↦ γq γpop MD"... }
      wp_pures. iApply "Φ"...
  Qed.
*)
Admitted.
End proof.
