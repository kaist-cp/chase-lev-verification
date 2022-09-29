From iris.algebra Require Import excl auth list.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import atomic.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import proofmode notation.
From iris.prelude Require Import options.

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
  deque_tokG :> inG Σ (authR (optionUR (exclR (listO valO)))) }.
Definition dequeΣ : gFunctors :=
  #[GFunctor (authR (optionUR (exclR (listO valO))))].
Global Instance subG_dequeΣ {Σ} : subG dequeΣ Σ → dequeG Σ.
Proof. solve_inG. Qed.

Section proof.
  Context `{!heapGS Σ, !dequeG Σ} (N : namespace).
  Notation iProp := (iProp Σ).
  Let dequeN := N .@ "deque".

  Definition deque_inv (γq : gname) (arr top bot : loc) : iProp :=
    ∃ (t b : nat) (l : list val),
      top ↦ #t ∗ bot ↦{#1/2} #b ∗ arr ↦∗{#1/2} l ∗
      own γq (● (Some ((Excl (take b (drop t l)) )))) ∗
      ⌜length l = CAP_CONST⌝.

  Definition is_deque (γq : gname) (q : val) : iProp :=
    ∃ (arr top bot : loc),
      ⌜q = (#arr, #top, #bot)%V⌝ ∗
      inv dequeN (deque_inv γq arr top bot).
  Global Instance is_deque_persistent γq q :
    Persistent (is_deque γq q) := _.

  Definition deque_content (γq : gname) (l : list val) : iProp :=
    (* TODO: use ghost_var? *)
    (own γq (◯ Excl' l))%I.

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
    wp_lam. wp_alloc arr as "arr↦". { unfold CAP_CONST. lia. }
    wp_pures. wp_alloc b as "[b↦1 b↦2]". wp_alloc t as "t↦".
    iMod (own_alloc (● (Some (Excl [])) ⋅ ◯ (Some (Excl []))))
      as (γq) "[● ◯]". { by apply auth_both_valid_discrete. }
    iMod (inv_alloc dequeN _ (deque_inv γq arr t b)
      with "[t↦ b↦1 arr↦ ●]") as "Inv".
    { iNext. iExists 0, 0, _.
      rewrite take_0. iFrame "t↦ b↦1 arr↦". iSplit; auto. }
    wp_pures. iModIntro. iApply "HΦ".
    iSplit; auto.
    - iExists _, _, _; iSplit; auto.
    - iSplitR "b↦2"; auto. iExists _,_,_,0; iSplit; auto.
  Qed.

  Lemma push_spec γq q (v : val) :
    is_deque γq q -∗
    own_deque γq q -∗
    <<< ∀∀ l : list val, deque_content γq l >>>
      push q v @ ↑N
    <<< deque_content γq (l ++ [v]), RET #() >>>.
  Proof.
    iIntros "#Is Own" (Φ) "AU".
      iDestruct "Own" as (arr top bot b l) "(-> & %HL & b👑 & arr👑)".
      iDestruct "Is" as (arr' top' bot') "[%Is Inv]".
      injection Is as [= <- <- <-].
    wp_lam. unfold code.arr, code.bot. wp_pures.

    (* load bot *)
    wp_bind (! _)%E.
    iInv "Inv" as (t1 b1 l1) "(t↦ & >b↦ & >arr↦ & ● & >%HL1)".
      iDestruct (mapsto_agree with "b↦ b👑") as "%".
      injection H as [= <-]. clear b.
      assert (l = l1) by admit.
      subst. clear HL.
    wp_load.
      
    iModIntro. iSplitL "t↦ b↦ arr↦ ●".
    { iExists _,_,_. iFrame "t↦ b↦ arr↦". iSplit; auto. }
    wp_pures. case_bool_decide.
    { wp_pures. iApply loop_spec; eauto. iNext. by iIntros. }
    rename H into BOUND.
    wp_pures.

    (* store value *)
    wp_bind (_ <- _)%E.
    iInv "Inv" as (t2 b2 l2) "(t↦ & >b↦ & >arr↦ & ● & >%HL2)".
      iDestruct (mapsto_agree with "b↦ Own") as "%".
      injection H as [=].
      rewrite <- H in BOUND. rewrite <- H. clear H b1 t1 l1.
    iApply (wp_store_offset with "arr↦").
    { rewrite lookup_lt_is_Some. lia. }
    iNext. iIntros "arr↦". iModIntro.
    iSplitL "t↦ b↦ arr↦ ●".
    { iNext. iExists _, _, _. iFrame "t↦ b↦ arr↦".
      iSplit; auto.
      2: by rewrite insert_length. admit. }
    wp_pures.

    (* store bot *)
    iInv "Inv" as (t3 b3 l3) "(t↦ & >b↦ & arr↦ & >● & HL3)".
      iDestruct (mapsto_agree with "b↦ Own") as "%".
      injection H as [=].
      rewrite <- H in BOUND. rewrite <- H. clear H b2 t2 HL2 l2.
    iMod "AU" as (l) "[Cont [_ Commit]]".
      unfold deque_content.

    iCombine "Own b↦" as "b↦". wp_store.
    assert ((Z.of_nat b3 + 1)%Z = Z.of_nat (b3 + 1)) as -> by lia.
    iModIntro. iSplitL "t↦ b↦ REST".
    { unfold deque_inv. iExists _,_,_; iFrame. admit. }
  Admitted.
End proof.
