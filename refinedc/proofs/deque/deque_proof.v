From iris.algebra Require Import csum excl auth cmra_big_op.
From iris.algebra Require Import big_op gset frac agree.
From iris.bi Require Import atomic.
From refinedc.typing Require Import typing.
From refinedc.project.ex.deque Require Import deque_def.
From refinedc.project.ex.deque Require Import generated_code generated_spec.
Set Default Proof Using "Type".

Section helper.
  Lemma deque_offset_arr q :
    q +ₗ Z.of_nat (offset_of_idx [(Some "arr", mk_array_layout i32 16);
      (Some "size", it_layout i32); (Some "top", it_layout i32); (Some "bot", it_layout i32)] 0)
    = q at{struct_deque}ₗ "arr".
  Proof. auto. Qed.
  Lemma deque_offset_size q :
    q +ₗ Z.of_nat (offset_of_idx [(Some "arr", mk_array_layout i32 16);
      (Some "size", it_layout i32); (Some "top", it_layout i32); (Some "bot", it_layout i32)] 1)
    = q at{struct_deque}ₗ "size".
  Proof. auto. Qed.
  Lemma deque_offset_top q :
    q +ₗ Z.of_nat (offset_of_idx [(Some "arr", mk_array_layout i32 16);
      (Some "size", it_layout i32); (Some "top", it_layout i32); (Some "bot", it_layout i32)] 2)
    = q at{struct_deque}ₗ "top".
  Proof. auto. Qed.
  Lemma deque_offset_bot q :
    q +ₗ Z.of_nat (offset_of_idx [(Some "arr", mk_array_layout i32 16);
      (Some "size", it_layout i32); (Some "top", it_layout i32); (Some "bot", it_layout i32)] 3)
    = q at{struct_deque}ₗ "bot".
  Proof. auto. Qed.

End helper.

Section type.
  Context `{!typeG Σ} `{!globalG Σ} `{!dequeG Σ}.

  Lemma type_push (global_push : loc) :
    global_push ◁ᵥ global_push @ atomic_function_ptr type_of_push ⊤ -∗
    atomic_typed_function ⊤ (impl_push global_push) type_of_push.
  Proof.
    start_function "push" ([[[g q] n] v]) => arg_q arg_v local_sz local_b.
    prepare_parameters (g q n v).

    liRStepUntil @typed_read_end.
    iRename select (own_deque _ _ _) into "Q". unfold own_deque.
      iDestruct "Q" as (γq γpop γm sz arr top bot b l) "(%G & q & %Hlen & Pop & arr↦ & b↦)".
      iEval (unfold ty_own; simpl) in "q".
      iDestruct "q" as "(%qlay & _ & qbound & qarr & qsz & qtop & qbot & _)".
      rewrite deque_offset_arr deque_offset_size deque_offset_top deque_offset_bot.
      (* equalities remain at # because liRStep removes pure equalities *)
      iEval (unfold ty_own; simpl) in "qarr". iDestruct "qarr" as "#Hqarr".
      iEval (unfold ty_own; simpl) in "qsz". iDestruct "qsz" as "#Hqsz".
      iEval (unfold ty_own; simpl) in "qtop". iDestruct "qtop" as "#Hqtop".
      iEval (unfold ty_own; simpl) in "qbot". iDestruct "qbot" as "#Hqbot".
    iAssert (⌜bot = q at{struct_deque}ₗ "bot"⌝%I) as "%HB"; auto. rewrite <- HB. clear HB.

unfold typed_read_end. iIntros "bot2".
iModIntro. iExists (1/2)%Qp, (i2v b i32), (int i32). iSplit; first admit. iSplit; first admit.
iFrame "b↦". iSplit; first admit. iNext. iIntros (st) "b↦".
iIntros "#bty". iModIntro.
iExists (place x2), (int i32). iSplit; first admit. iFrame "bot2". iIntros "argq (qwe & _)".

    (*liRStepUntil @typed_read_end.*)
    do 3 liRStep; liShow.
    iRename select (inv _ _) into "Inv".
    iInv "Inv" as "WEQE".


  Qed.
End type.
