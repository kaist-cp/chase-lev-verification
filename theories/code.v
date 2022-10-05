From iris.algebra Require Import excl auth list.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import invariants ghost_var.
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
  deque_tokG :> ghost_varG Σ (list val) }.
Definition dequeΣ : gFunctors :=
  #[ghost_varΣ (list val)].
Global Instance subG_dequeΣ {Σ} : subG dequeΣ Σ → dequeG Σ.
Proof. solve_inG. Qed.

Section proof.
  Context `{!heapGS Σ, !dequeG Σ} (N : namespace).
  Notation iProp := (iProp Σ).
  (* TODO: do we really need submasks? *)
  Let dequeN := N .@ "deque".

  (* TODO: change l to ↦∗{#1} & make another ghost_var in deque_content?
     (see msqueue) *)
  Definition deque_inv (γq : gname) (arr top bot : loc) : iProp :=
    ∃ (t b : nat) (l : list val),
      top ↦ #t ∗ bot ↦{#1/2} #b ∗ arr ↦∗{#1/2} l ∗
      ghost_var γq (1/2) (slice l t b) ∗
      ⌜t ≤ b⌝ ∗
      ⌜length l = CAP_CONST⌝.

  Definition is_deque (γq : gname) (q : val) : iProp :=
    ∃ (arr top bot : loc),
      ⌜q = (#arr, #top, #bot)%V⌝ ∗
      inv dequeN (deque_inv γq arr top bot).
  Global Instance is_deque_persistent γq q :
    Persistent (is_deque γq q) := _.

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

  Lemma new_deque_spec :
    {{{ True }}}
      new_deque #()
    {{{ γq q, RET q;
      is_deque γq q ∗ deque_content γq [] ∗
      own_deque γq q
    }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_lam. wp_alloc arr as "[arr↦1 arr↦2]". { unfold CAP_CONST. lia. }
    wp_pures. wp_alloc b as "[b↦1 b↦2]". wp_alloc t as "t↦".
    iMod (ghost_var_alloc []) as (γq) "[γ1 γ2]".
    iMod (inv_alloc dequeN _ (deque_inv γq arr t b)
      with "[t↦ b↦1 arr↦1 γ1]") as "Inv".
    { iNext. iExists 0, 0, _. iFrame "t↦ b↦1 arr↦1". auto. }
    wp_pures. iModIntro. iApply "HΦ".
    iSplit; auto.
    - iExists _, _, _. auto.
    - iSplitR "b↦2 arr↦2"; auto.
      iExists _,_,_,0,_. iFrame. auto.
  Qed.

  Lemma push_spec γq q (v : val) :
    is_deque γq q -∗
    own_deque γq q -∗
    <<< ∀∀ l : list val, deque_content γq l >>>
      push q v @ ↑N
    <<< deque_content γq (l ++ [v]) ∗ own_deque γq q, RET #() >>>.
  Proof with auto; try lia.
    iIntros "#Is Own" (Φ) "AU".
      iDestruct "Own" as (arr top bot b l) "(-> & %HL & b👑 & arr👑)".
      iDestruct "Is" as (arr' top' bot') "[%Is Inv]".
      injection Is as [= <- <- <-].
    wp_lam. unfold code.arr, code.bot. wp_pures.

    (* load bot *)
    wp_bind (! _)%E.
    iInv "Inv" as (t1 b1 l1) ">(t↦ & b↦ & arr↦ & γ & [%Htb1 %HL1])".
      iDestruct (mapsto_agree with "b↦ b👑") as "%".
        injection H as [=]. apply Nat2Z.inj in H.
      iDestruct (array_agree with "arr↦ arr👑") as "%"...
      subst. clear HL.
    wp_load.
    
    iModIntro. iSplitL "t↦ b↦ arr↦ γ".
      { iExists _,_,_. iFrame "t↦ b↦ arr↦"... }
    wp_pures. case_bool_decide.
      { wp_pures. iApply loop_spec... iNext. iIntros... }
    assert (b < CAP_CONST)... rename H0 into BOUND. clear H.
    wp_pures.

    (* store value *)
    wp_bind (_ <- _)%E.
    iInv "Inv" as (t2 b2 l2) ">(t↦ & b↦ & arr↦ & γ & [%Htb2 %HL2])".
      iDestruct (mapsto_agree with "b↦ b👑") as "%".
        injection H as [=]. apply Nat2Z.inj in H.
      iDestruct (array_agree with "arr↦ arr👑") as "%"...
      subst. clear t1 Htb1 HL1.
    iCombine "arr↦ arr👑" as "arr↦".
    iApply (wp_store_offset with "arr↦").
      { rewrite lookup_lt_is_Some... }
    iNext. iIntros "[arr↦ arr👑]". iModIntro.
    iSplitL "t↦ b↦ arr↦ γ".
    { iNext. iExists t2, b, _. iFrame "t↦ b↦ arr↦".
      rewrite slice_insert_right... iFrame. rewrite insert_length... }
    wp_pures.
    replace (Z.of_nat b + 1)%Z with (Z.of_nat (S b))...

    (* store bot *)
    iInv "Inv" as (t3 b3 l3) ">(t↦ & b↦ & arr↦ & γ1 & [%Htb3 %HL3])".
      iDestruct (mapsto_agree with "b↦ b👑") as "%".
        injection H as [=]. apply Nat2Z.inj in H.
      iDestruct (array_agree with "arr↦ arr👑") as "%"; subst.
        { rewrite insert_length... }
      rewrite insert_length in HL3. clear t2 Htb2 HL2.
    iMod "AU" as (l') "[Cont [_ Commit]]".
      unfold deque_content.
      iDestruct (ghost_var_agree with "γ1 Cont") as "%"; subst.
      rewrite <- slice_extend_right... 2: rewrite list_lookup_insert...
    iCombine "b↦ b👑" as "b↦". wp_store.
    iDestruct "b↦" as "[b↦ b👑]".
    iMod (ghost_var_update_2 (slice (<[b:=v]> l) t3 (S b))
      with "γ1 Cont") as "[γ1 Cont]". { rewrite Qp.half_half... }
    iMod ("Commit" with "[Cont b👑 arr👑]") as "Φ".
    { iFrame. iExists _,_,_,(S b),_; iFrame. repeat iSplit...
      rewrite insert_length... }
    iModIntro. iModIntro.
    
    iFrame. unfold deque_inv. iNext. iExists _,_,_.
    iFrame "t↦ arr↦ γ1"; iSplit... rewrite insert_length...
  Qed.
End proof.