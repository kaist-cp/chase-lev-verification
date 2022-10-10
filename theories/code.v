From iris.algebra Require Import excl auth list.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import invariants ghost_var mono_nat.
From iris.program_logic Require Import atomic.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import proofmode notation.
From iris.prelude Require Import options.
From chase_lev Require Import helpers.

(*
  We use a finite length list without resizing;
  The push function diverges if bot gets out of bound.
  +--+--+--+--+--+--+--+--
  |  |10|20|30|40|  |  |   ..
  +--+--+--+--+--+--+--+--
      ^           ^
      |           |
      top (steal) bot (push, pop)
*)

Section code.
  Definition CAP_CONST : nat := 10.
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
  Definition steal : val :=
    λ: "deque",
      let: "array" := arr "deque" in
      let: "t" := !(top "deque") in
      let: "b" := !(bot "deque") in
      if: "b" ≤ "t" then #()
      else if: CAS (top "deque") "t" ("t" + #1) then !("array" +ₗ "t")
      else #().
End code.

Class dequeG Σ := DequeG {
    deque_tokG :> ghost_varG Σ (list val);
    mono_natG :> mono_natG Σ
  }.
Definition dequeΣ : gFunctors :=
  #[ghost_varΣ (list val);
    mono_natΣ
  ].
Global Instance subG_dequeΣ {Σ} : subG dequeΣ Σ → dequeG Σ.
Proof. solve_inG. Qed.

(* TODO: move this to helpers.v *)
Section Inbound.
  Definition deque_bound (t b : nat) (l : list val) :=
    t ≤ b /\ b < length l /\ length l = CAP_CONST.

  Lemma deque_bound_init : deque_bound 0 0 (replicate (Z.to_nat CAP_CONST) #0).
  Proof.
    unfold deque_bound. repeat split; auto.
    rewrite replicate_length. replace (Z.to_nat CAP_CONST) with 10 by auto. lia.
  Qed.

  Lemma deque_bound_2_length t1 b1 t2 b2 l1 l2 :
    deque_bound t1 b1 l1 → deque_bound t2 b2 l2 → length l1 = length l2.
  Admitted.

  Lemma deque_bound_insert t b l i v :
    deque_bound t b l → i < length l → deque_bound t b (<[b:=v]> l).
  Admitted.

  Lemma deque_bound_extend_right t b l :
    deque_bound t b l → b < length l → deque_bound t (S b) l.
  Admitted.

  Lemma deque_bound_shrink_left t b l : 
    deque_bound t b l → t < b → deque_bound (S t) b l.
  Admitted.
End Inbound.

Section RA.
  Context `{!heapGS Σ, !dequeG Σ} (N : namespace).
  Notation iProp := (iProp Σ).

  (* TODO [URGENT]: we actually need mono_list of [0..t), not just mono_nat of t *)
  Definition mono_toparr (γt : gname) (t : nat) (l : list val) : iProp :=
    let tl := match l with | [] => (2*t) | _ => (2*t+1) end in
    mono_nat_auth_own γt 1 tl.

  Definition mono_toparr_lb (γt : gname) (t : nat) (l : list val) : iProp :=
    let tl := match l with | [] => (2*t) | _ => (2*t+1) end in
    mono_nat_lb_own γt tl.

  Lemma mono_toparr_get_lb (γt : gname) (t : nat) (l : list val) :
    mono_toparr γt t l ==∗ mono_toparr γt t l ∗ mono_toparr_lb γt t l.
  Proof.
  Admitted.

  Lemma mono_toparr_lb_own_top (γt : gname) (t1 t2 : nat) (l1 l2 : list val) :
    mono_toparr γt t1 l1 -∗ mono_toparr_lb γt t2 l2 -∗ ⌜t2 ≤ t1⌝.
  Proof.
  Admitted.

  Lemma mono_toparr_append (γt : gname) (l1 l2 : list val) (t : nat) :
    mono_toparr γt t l1 ==∗ mono_toparr γt t (l1 ++ l2).
  Proof.
    iIntros "mta". destruct l2. { rewrite app_nil_r. auto. }
    destruct l1; last first. { unfold mono_toparr. auto. }
    unfold mono_toparr. simpl.
    iMod (mono_nat_own_update (t+(t+0)+1) with "mta") as "[mta _]"; auto. lia.
  Qed.

  Lemma mono_toparr_top (γt : gname) (t1 t2 : nat) (l1 l2 : list val) :
    t1 ≤ t2 →
    mono_toparr γt t1 l1 ==∗ mono_toparr γt t2 l2.
  Admitted.
End RA.

Section proof.
  Context `{!heapGS Σ, !dequeG Σ} (N : namespace).
  Notation iProp := (iProp Σ).
  (* TODO: do we really need submasks? *)
  Let dequeN := N .@ "deque".

  (* TODO: change l to ↦∗{#1} & make another ghost_var in deque_content?
     (see msqueue) *)
  Definition deque_inv (γq γt : gname) (arr top bot : loc) : iProp :=
    ∃ (t b : nat) (l : list val),
      top ↦ #t ∗ bot ↦{#1/2} #b ∗ arr ↦∗{#1/2} l ∗
      ghost_var γq (1/2) (slice l t b) ∗
      mono_toparr γt t (slice l t b) ∗
      ⌜deque_bound t b l⌝.

  Definition is_deque (γq γt : gname) (q : val) : iProp :=
    ∃ (arr top bot : loc),
      ⌜q = (#arr, #top, #bot)%V⌝ ∗
      inv dequeN (deque_inv γq γt arr top bot).
  Global Instance is_deque_persistent γq γt q :
    Persistent (is_deque γq γt q) := _.

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

  Lemma new_deque_spec :
    {{{ True }}}
      new_deque #()
    {{{ γq γt q, RET q;
      is_deque γq γt q ∗ deque_content γq [] ∗
      own_deque γq q
    }}}.
  Proof with autoall.
    iIntros (Φ) "_ HΦ".
    wp_lam. wp_alloc arr as "[arr↦1 arr↦2]"...
    wp_pures. wp_alloc b as "[b↦1 b↦2]". wp_alloc t as "t↦".
    iMod (ghost_var_alloc []) as (γq) "[γ1 γ2]".
    iMod (mono_nat_own_alloc 0) as (γt) "[γt _]".
    iMod (inv_alloc dequeN _ (deque_inv γq γt arr t b)
      with "[t↦ b↦1 arr↦1 γ1 γt]") as "Inv".
    { iNext. iExists 0, 0, _. iFrame "t↦ b↦1 arr↦1". iFrame.
      iPureIntro. apply deque_bound_init. }
    wp_pures. iModIntro. iApply "HΦ". iSplit.
    - iExists _, _, _...
    - iSplitR "b↦2 arr↦2"... iExists _,_,_,0,_. iFrame...
  Qed.

  Lemma push_spec γq γt q (v : val) :
    is_deque γq γt q -∗
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
    iMod (mono_toparr_append _ (slice (<[b:=v]> l) t3 b) [v] with "mta") as "mta".
      rewrite <- slice_extend_right... 2: rewrite list_lookup_insert...
    iMod ("Commit" with "[Cont b👑 arr👑]") as "Φ".
    { iFrame. iExists _,_,_,(S b),_; iFrame. iSplit... rewrite insert_length... }
    iModIntro. iModIntro.
    
    iFrame. unfold deque_inv. iNext. iExists _,_,_.
    iFrame "t↦ b↦ arr↦ γ". iSplit...
    iPureIntro. apply deque_bound_extend_right...
  Qed.

  Lemma steal_spec γq γt q :
    is_deque γq γt q -∗
    <<< ∀∀ l : list val, deque_content γq l >>>
      steal q @ ↑N
    <<< ∃∃ (l' : list val) (v : val),
      deque_content γq l' ∗
      match v with
      | #() => ⌜l' = l⌝
      | _ => ⌜l = [v] ++ l'⌝
      end, RET v >>>.
  Proof with autoall.
    iIntros "#Is" (Φ) "AU".
      iDestruct "Is" as (arr top bot) "[%Is Inv]". subst.
    wp_lam. unfold code.arr, code.top, code.bot. wp_pures.

    (* load top *)
    wp_bind (! _)%E.
    iInv "Inv" as (t1 b1 l1) ">(t↦ & b↦ & arr↦ & γ & mta & %BOUND1)".
      iMod (mono_toparr_get_lb with "mta") as "[mta #mtlb1]".
    wp_load.
    iModIntro. iSplitL "t↦ b↦ arr↦ γ mta".
      { iExists _,_,_. iFrame "t↦ b↦ arr↦ γ"... }
    wp_pures.

    (* load bot *)
    wp_bind (! _)%E.
    iInv "Inv" as (t2 b2 l2) ">(t↦ & b↦ & arr↦ & γ & mta & %BOUND2)".
      iMod (mono_toparr_get_lb with "mta") as "[mta #mtlb2]".
      iDestruct (mono_toparr_lb_own_top with "mta mtlb1") as "%Ht12".
    wp_load.
    iModIntro. iSplitL "t↦ b↦ arr↦ γ mta".
      { iExists _,_,_. iFrame "t↦ b↦ arr↦ γ"... }
    wp_pures.

    (* no chance to steal *)
    case_bool_decide; wp_pures.
    { admit. }

    (* cas top *)
    wp_bind (CmpXchg _ _ _)%E.
    iInv "Inv" as (t3 b3 l3) ">(t↦ & b↦ & arr↦ & γ & mta & %BOUND3)".
      iDestruct (mono_toparr_lb_own_top with "mta mtlb2") as "%Ht23".
    destruct (decide (t3 = t1)).
    - (* success *)
      assert (t1 = t2)... subst. wp_cmpxchg_suc.
      assert (t2 < b3) by admit.
      replace (Z.of_nat t2 + 1)%Z with (Z.of_nat (S t2))...
      iMod (mono_toparr_top _ _ t2 (S t2) with "mta") as "mta"...
      iMod "AU" as (l') "[Cont [_ Commit]]".
        unfold deque_content.
        iDestruct (ghost_var_agree with "γ Cont") as "%". subst.
        iMod (ghost_var_update_2 (slice l3 (S t2) b3) with "γ Cont") as "[γ Cont]".
          { rewrite Qp.half_half... }
        assert (is_Some (l3 !! t2)) as [k HLk].
          { rewrite lookup_lt_is_Some... }
        iMod ("Commit" $! _ k with "[Cont]").
          { iFrame. admit. }
      iModIntro. iSplitL "t↦ b↦ arr↦ γ mta".
        { iExists _,_,_. iFrame "t↦ b↦ arr↦ γ mta".
          iNext. iPureIntro. apply deque_bound_shrink_left... }
      wp_pures.
  Admitted.
End proof.
