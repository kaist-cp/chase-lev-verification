From iris.algebra Require Import excl auth list.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import atomic.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import proofmode notation atomic_heap.
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
  Definition CAP_CONST := 10.
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

Section proof.
  Context `{!heapGS Σ} (N : namespace).
  Notation iProp := (iProp Σ).
  Let dequeN := N .@ "deque".

  Definition deque_inv (γq : gname) (arr top bot : loc) : iProp :=
    (∃ (t b : nat), top ↦ #t ∗ bot ↦ #b) ∗
    (* the following is not true, we need big sepL ∗.
    ∀ (i : nat), ⌜0 ≤ i < CAP_CONST⌝ -∗
      ∃ v, (arr +ₗ i) ↦ v.
      *)
    True.

  Definition is_deque (γq : gname) (q : val) : iProp :=
    ∃ (arr top bot : loc),
      ⌜q = (#arr, #top, #bot)%V⌝ ∗
      inv dequeN (deque_inv γq arr top bot).
  Global Instance is_deque_persistent γq q :
    Persistent (is_deque γq q) := _.

  Definition deque_content (γq : gname) (q : val)
  (l : list val) : iProp :=
    True.

  Definition own_deque (γq : gname) (q : val) : iProp :=
    True.
  
  Lemma loop_spec v :
    {{{ True }}} loop #v {{{ RET #(); False }}}.
  Proof.
    iIntros (Φ) "_ HΦ". wp_rec. iLöb as "IH". wp_rec.
    by iApply "IH".
  Qed.

  Lemma push_spec γq q (v : val) :
    is_deque γq q -∗
    own_deque γq q -∗
    <<< ∀∀ l : list val, deque_content γq q l >>>
      push q v @ ↑N
    <<< True, RET #() >>>.
  Proof.
    iIntros "#Is Own" (Φ) "AU".
    iDestruct "Is" as (arr top bot) "[%Is Inv]". subst.
    wp_lam. unfold code.arr, code.bot. wp_pures.

    (* load bot *)
    wp_bind (! _)%E.
    iInv "Inv" as "[>Invtb >Invarr]".
    iDestruct "Invtb" as (t b) "[t↦ b↦]". wp_load.
    iModIntro. iSplitL "t↦ b↦ Invarr".
    { unfold deque_inv. eauto with iFrame. }
    wp_pures. case_bool_decide.
    { wp_pures. iApply loop_spec; eauto. iNext. by iIntros. }
    wp_pures.

    (* store value *)
    wp_bind (_ <- _)%E.
    iInv "Inv" as "[>Invtb >Invarr]".
  Admitted.
End proof.
