From iris.algebra Require Import excl auth list.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import invariants ghost_var mono_nat.
From iris.program_logic Require Import atomic.
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
      ("array", ref #0, ref #0). (* array, top, bottom *)
  
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
  
(* TODO: change return value to (bool, val) so that we can push and pop #() *)
  Definition pop : val :=
    λ: "deque",
      let: "array" := arr "deque" in
      let: "b" := !(bot "deque") in
      bot "deque" <- "b" - #1 ;;
      let: "t" := !(top "deque") in
      if: "b" ≤ "t" then (* empty pop *)
        bot "deque" <- "b" ;; #()
      else if: "t" < "b" - #1 then (* normal case *)
        !("array" +ₗ ("b" - #1))
      else (* might conflict with steal *)
      let: "ok" := CAS (top "deque") "t" ("t" + #1) in
      bot "deque" <- "b" ;;
      if: "ok" then !("array" +ₗ "t") (* popped *)
      else #(). (* stolen *)

  (* NOTE: b ≤ t doesn't necessarily mean the deque was empty!
    It can also be the case that there was one element and
    the owner thread prematurely decremented b trying to pop. *)
  (* TODO: change to NONE/SOME *)
  Definition steal : val :=
    λ: "deque",
      let: "array" := arr "deque" in
      let: "t" := !(top "deque") in
      let: "b" := !(bot "deque") in
      if: "b" ≤ "t" then (#false, #())
      else if: CAS (top "deque") "t" ("t" + #1)
      then (#true, !("array" +ₗ "t"))
      else (#false, #()).
End code.

Class dequeG Σ := DequeG {
    deque_tokG :> ghost_varG Σ (list val);
    mono_listG :> mono_listG val Σ;
    mono_natG :> mono_natG Σ
  }.
Definition dequeΣ : gFunctors :=
  #[ghost_varΣ (list val);
    mono_listΣ val;
    mono_natΣ
  ].
Global Instance subG_dequeΣ {Σ} : subG dequeΣ Σ → dequeG Σ.
Proof. solve_inG. Qed.

Section RA.
  Context `{!heapGS Σ, !dequeG Σ} (N : namespace).
  Notation iProp := (iProp Σ).

  Definition mono_deque_auth_own (γm : gname) (l : list val) (t b : nat) : iProp :=
    ∃ (γl γmb : gname),
    ⌜γm = encode (γl, γmb)⌝ ∗
    ⌜deque_bound t b l⌝ ∗
    mono_list_auth_own γl 1 (take t l) ∗
    mono_nat_auth_own γmb 1 (
      2 * t + (if decide(t < b) then 1 else 0)
    ).

  Definition mono_deque_lb_own (γm : gname) (l : list val) (t b : nat) : iProp :=
    ∃ (γl γmb : gname),
    ⌜γm = encode (γl, γmb)⌝ ∗
    ⌜deque_bound t b l⌝ ∗
    mono_list_lb_own γl (take t l) ∗
    mono_nat_lb_own γmb (
      2 * t + (if decide(t < b) then 1 else 0)
    ).

  Lemma mono_deque_own_alloc l :
    ⌜length l = CAP_CONST⌝ ==∗ ∃ γ, mono_deque_auth_own γ l 0 0.
  Proof.
    iIntros (H).
    iMod (mono_list_own_alloc []) as (γl) "[L _]".
    iMod (mono_nat_own_alloc 0) as (γmb) "[N _]".
    iExists (encode (γl, γmb)). iModIntro.
    iExists _,_. iSplit; iFrame; auto.
    iPureIntro. by apply deque_bound_init.
  Qed.

  Lemma mono_deque_get_lb γm l t b :
    mono_deque_auth_own γm l t b ==∗ mono_deque_auth_own γm l t b ∗ mono_deque_lb_own γm l t b.
  Proof.
  Admitted.

  Lemma mono_deque_auth_lb γm l1 t1 b1 l2 t2 b2 :
    mono_deque_auth_own γm l1 t1 b1 -∗ mono_deque_lb_own γm l2 t2 b2 -∗
    ⌜t2 ≤ t1 ∧ take t2 l2 = take t2 l1⌝.
  Proof.
  Admitted.
(*
  Lemma mono_deque_append (γm : gname) (l1 l2 : list val) (t : nat) :
    mono_deque_auth_own γm t l1 ==∗ mono_deque_auth_own γm t (l1 ++ l2).
  Proof.
    iIntros "mta". destruct l2. { rewrite app_nil_r. auto. }
    destruct l1; last first. { unfold mono_deque. auto. }
    unfold mono_deque. simpl.
    iMod (mono_nat_own_update (t+(t+0)+1) with "mta") as "[mta _]"; auto. lia.
  Qed.

  Lemma mono_deque_top (γm : gname) (t1 t2 : nat) (l1 l2 : list val) :
    t1 ≤ t2 →
    mono_deque_auth_own γm t1 l1 ==∗ mono_deque_auth_own γm t2 l2.
  Admitted.
  *)

  Lemma mono_deque_top_nonempty γm t l1 b1 l2 b2 :
    t < b2 →
    mono_deque_auth_own γm l1 t b1 -∗ mono_deque_lb_own γm l2 t b2 -∗
    ⌜t < b1⌝.
  Admitted.

  Lemma mono_deque_update_top γm t2 l t1 b :
    t1 ≤ t2 →
    mono_deque_auth_own γm l t1 b ==∗ mono_deque_auth_own γm l t2 b.
  Admitted.
End RA.

Section proof.
  Context `{!heapGS Σ, !dequeG Σ} (N : namespace).
  Notation iProp := (iProp Σ).
  (* TODO: do we really need submasks? *)
  Let dequeN := N .@ "deque".

  (* TODO: change l to ↦∗{#1} & make another ghost_var in deque_content?
     (see msqueue) *)
  Definition deque_inv (γq γm : gname) (arr top bot : loc) : iProp :=
    ∃ (t b : nat) (l : list val),
      ⌜deque_bound t b l⌝ ∗
      top ↦ #t ∗ bot ↦{#1/2} #b ∗ arr ↦∗{#1/2} l ∗
      ghost_var γq (1/2) (slice l t b) ∗
      mono_deque_auth_own γm l t b.

  Definition is_deque (γq γm : gname) (q : val) : iProp :=
    ∃ (arr top bot : loc),
      ⌜q = (#arr, #top, #bot)%V⌝ ∗
      inv dequeN (deque_inv γq γm arr top bot).
  Global Instance is_deque_persistent γq γm q :
    Persistent (is_deque γq γm q) := _.

  Definition deque_content (γq : gname) (frag : list val) : iProp :=
    ghost_var γq (1/2) frag.

  Definition own_deque (γq : gname) (q : val) : iProp :=
    ∃ (arr top bot : loc) (b : nat) (l : list val),
      ⌜q = (#arr, #top, #bot)%V⌝ ∗
      ⌜length l = CAP_CONST⌝ ∗
      bot ↦{#1/2} #b ∗ arr ↦∗{#1/2} l.
  
  Lemma loop_spec v :
    {{{ True }}} loop #v {{{ RET #(); False }}}.
  Proof.
    iIntros (Φ) "_ HΦ". wp_rec. iLöb as "IH". wp_rec.
    by iApply "IH".
  Qed.

  Ltac autoall :=
    auto; try by (unfold deque_bound in *; unfold CAP_CONST in *; lia).

    (*
  Lemma new_deque_spec :
    {{{ True }}}
      new_deque #()
    {{{ γq γm q, RET q;
      is_deque γq γm q ∗ deque_content γq [] ∗
      own_deque γq q
    }}}.
  Proof with autoall.
    iIntros (Φ) "_ HΦ".
    wp_lam. wp_alloc arr as "[arr↦1 arr↦2]"...
    wp_pures. wp_alloc b as "[b↦1 b↦2]". wp_alloc t as "t↦".
    iMod (ghost_var_alloc []) as (γq) "[γ1 γ2]".
    iMod (mono_deque_own_alloc) as (γm) "γm".
    iMod (inv_alloc dequeN _ (deque_inv γq γm arr t b)
      with "[t↦ b↦1 arr↦1 γ1 γm]") as "Inv".
    { iNext. iExists 0, 0, _. iFrame "t↦ b↦1 arr↦1". iFrame.
      iPureIntro. apply deque_bound_init. }
    wp_pures. iModIntro. iApply "HΦ". iSplit.
    - iExists _, _, _...
    - iSplitR "b↦2 arr↦2"... iExists _,_,_,0,_. iFrame...
  Qed.

  Lemma push_spec γq γm q (v : val) :
    is_deque γq γm q -∗
    own_deque γq q -∗
    <<< ∀∀ l : list val, deque_content γq l >>>
      push q v @ ↑N
    <<< deque_content γq (l ++ [v]) ∗ own_deque γq q, RET #() >>>.
  Proof with autoall.
    iIntros "#Is Own" (Φ) "AU".
      iDestruct "Own" as (arr top bot b l) "(-> & %HL & b👑 & arr👑)".
      iDestruct "Is" as (arr' top' bot') "[%Is Inv]".
      injection Is as [= <- <- <-].
    wp_lam. unfold code.arr, code.bot. wp_pures.

    (* load bot *)
    wp_bind (! _)%E.
    iInv "Inv" as (t1 b1 l1) ">(t↦ & b↦ & arr↦ & γ & mta & %BOUND1)".
      iDestruct (mapsto_agree with "b↦ b👑") as "%".
        injection H as [=]. apply Nat2Z.inj in H.
      iDestruct (array_agree with "arr↦ arr👑") as "%"... subst.
    wp_load.
    
    iModIntro. iSplitL "t↦ b↦ arr↦ γ mta".
      { iExists _,_,_. iFrame "t↦ b↦ arr↦ γ"... }
    wp_pures. case_bool_decide as HbC.
      { wp_pures. iApply loop_spec... }
    wp_pures.

    (* store value *)
    wp_bind (_ <- _)%E.
    iInv "Inv" as (t2 b2 l2) ">(t↦ & b↦ & arr↦ & γ & mta & %BOUND2)".
      iDestruct (mapsto_agree with "b↦ b👑") as "%".
        injection H as [=]. apply Nat2Z.inj in H.
      iDestruct (array_agree with "arr↦ arr👑") as "%"...
      subst. clear t1 BOUND1.
    iCombine "arr↦ arr👑" as "arr↦".
    iApply (wp_store_offset with "arr↦"). 1: rewrite lookup_lt_is_Some...
    iNext. iIntros "[arr↦ arr👑]". iModIntro.
    iSplitL "t↦ b↦ arr↦ γ mta".
    { iNext. iExists t2, b, _. iFrame "t↦ b↦ arr↦".
      rewrite slice_insert_right... iFrame. iPureIntro.
      eapply (deque_bound_insert _ _ _ b)... }
    wp_pures.
    replace (Z.of_nat b + 1)%Z with (Z.of_nat (S b))...

    (* store bot *)
    iInv "Inv" as (t3 b3 l3) ">(t↦ & b↦ & arr↦ & γ & mta & %BOUND3)".
      iDestruct (mapsto_agree with "b↦ b👑") as "%".
        injection H as [=]. apply Nat2Z.inj in H.
      iDestruct (array_agree with "arr↦ arr👑") as "%"; subst.
        1: rewrite insert_length...
      clear t2 BOUND2.
    iMod "AU" as (l') "[Cont [_ Commit]]".
      unfold deque_content.
      iDestruct (ghost_var_agree with "γ Cont") as "%"; subst.
      rewrite <- slice_extend_right... 2: rewrite list_lookup_insert...
    iCombine "b↦ b👑" as "b↦". wp_store.
    iDestruct "b↦" as "[b↦ b👑]".
    iMod (ghost_var_update_2 (slice (<[b:=v]> l) t3 (S b))
      with "γ Cont") as "[γ Cont]". { rewrite Qp.half_half... }
    iMod (mono_deque_append _ (slice (<[b:=v]> l) t3 b) [v] with "mta") as "mta".
      rewrite <- slice_extend_right... 2: rewrite list_lookup_insert...
    iMod ("Commit" with "[Cont b👑 arr👑]") as "Φ".
    { iFrame. iExists _,_,_,(S b),_; iFrame. iSplit... rewrite insert_length... }
    iModIntro. iModIntro.
    
    iFrame. unfold deque_inv. iNext. iExists _,_,_.
    iFrame "t↦ b↦ arr↦ γ". iSplit...
    iPureIntro. apply deque_bound_extend_right...
  Qed.
  *)

  Lemma steal_spec γq γm q :
    is_deque γq γm q -∗
    <<< ∀∀ l : list val, deque_content γq l >>>
      steal q @ ↑dequeN
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
    iInv "Inv" as (t1 b1 l1) ">(%BOUND1 & t↦ & b↦ & arr↦ & γ & MD)".
      iMod (mono_deque_get_lb with "MD") as "[MD #MDlb1]".
    wp_load.
    iModIntro. iSplitL "t↦ b↦ arr↦ γ MD".
      { iExists _,_,_. iFrame "t↦ b↦ arr↦ γ"... }
    wp_pures.

    (* load bot *)
    wp_bind (! _)%E.
    iInv "Inv" as (t2 b2 l2) ">(%BOUND2 & t↦ & b↦ & arr↦ & γ & MD)".
      iMod (mono_deque_get_lb with "MD") as "[MD #MDlb2]".
      iDestruct (mono_deque_auth_lb with "MD MDlb1") as "[%Ht12 %HL12]".
    wp_load.
    iModIntro. iSplitL "t↦ b↦ arr↦ γ MD".
      { iExists _,_,_. iFrame "t↦ b↦ arr↦ γ"... }
    wp_pures.

    (* no chance to steal *)
    case_bool_decide; wp_pures.
    { iMod "AU" as (l) "[Cont [_ Commit]]".
      iMod ("Commit" $! l false #() with "[Cont]")... }

    (* cas top *)
    wp_bind (CmpXchg _ _ _)%E.
    iInv "Inv" as (t3 b3 l3) ">(%BOUND3 & t↦ & b↦ & arr↦ & γ & MD)".
      iDestruct (mono_deque_auth_lb with "MD MDlb2") as "[%Ht23 %HL23]".
    destruct (decide (t3 = t1)).
    - (* success *)
      assert (t1 = t2)... subst. wp_cmpxchg_suc.
        clear Ht12 Ht23.
      (* update ghost *)
      iDestruct (mono_deque_top_nonempty _ with "MD MDlb2") as "%Htb23"...
      replace (Z.of_nat t2 + 1)%Z with (Z.of_nat (S t2))...
      iMod (mono_deque_update_top _ _ (S t2) with "MD") as "MD"...
      iMod (mono_deque_get_lb with "MD") as "[MD #MDlb3]".
      (* AU *)
      iMod "AU" as (l') "[Cont [_ Commit]]".
        unfold deque_content.
        iDestruct (ghost_var_agree with "γ Cont") as "%". subst.
        iMod (ghost_var_update_2 (slice l3 (S t2) b3) with "γ Cont")
          as "[γ Cont]". { rewrite Qp.half_half... }
        assert (is_Some (l3 !! t2)) as [k HLk].
          { rewrite lookup_lt_is_Some... }
        iMod ("Commit" $! (slice l3 (S t2) b3) true k with "[Cont]").
          { iFrame. erewrite slice_shrink_left... }
      iModIntro. iSplitL "t↦ b↦ arr↦ γ MD".
        { iExists _,_,_. iFrame "t↦ b↦ arr↦ γ MD".
          iNext. iPureIntro. apply deque_bound_shrink_left... }
      wp_pures.
      (* load arr[t2] *)
      wp_bind (! _)%E.
      iInv "Inv" as (t4 b4 l4) ">(%BOUND4 & t↦ & b↦ & arr↦ & γ & MD)".
        iDestruct (mono_deque_auth_lb with "MD MDlb3") as "[%Ht34 %HL34]".
      assert (l4 !! t2 = Some k).
        { rewrite -(lookup_take _ (S t2))... rewrite -HL34 lookup_take... }
      iApply (wp_load_offset with "arr↦")... 1: eauto.
      iNext. iIntros "arr↦".
      iModIntro. iSplitL "t↦ b↦ arr↦ γ MD".
      { iExists _,_,_. iFrame "t↦ b↦ arr↦ γ MD"... }
      by wp_pures.
    - (* fail *)
      wp_cmpxchg_fail. { intro. injection H0... }
      iMod "AU" as (l) "[Cont [_ Commit]]".
      iMod ("Commit" $! l false #() with "[Cont]")...
      iModIntro. iSplitL "t↦ b↦ arr↦ γ MD".
      { iExists _,_,_. iFrame "t↦ b↦ arr↦ γ MD"... }
      by wp_pures.
  Unshelve. (* what namespace?? *)
  Admitted.
End proof.
