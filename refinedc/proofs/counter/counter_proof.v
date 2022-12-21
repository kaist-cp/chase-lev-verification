From iris.algebra Require Import csum excl auth cmra_big_op.
From iris.algebra Require Import big_op gset frac agree.
From iris.bi Require Import atomic.
From refinedc.typing Require Import typing.
From refinedc.project.ex.counter Require Import counter_def.
From refinedc.project.ex.counter Require Import generated_code generated_spec.
Set Default Proof Using "Type".

Section type.
  Context `{!typeG Σ} `{!globalG Σ} `{!counterG Σ}.

  Lemma auth_agree γ xs ys :
    own γ (● (Excl' xs)) -∗ own γ (◯ (Excl' ys)) -∗ ⌜xs = ys⌝.
  Proof.
    iIntros "Hγ● Hγ◯". by iDestruct (own_valid_2 with "Hγ● Hγ◯")
      as %[<-%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
  Qed.

  Lemma auth_update γ ys xs1 xs2 :
  own γ (● (Excl' xs1)) -∗ own γ (◯ (Excl' xs2)) ==∗
    own γ (● (Excl' ys)) ∗ own γ (◯ (Excl' ys)).
  Proof.
    iIntros "Hγ● Hγ◯".
    iMod (own_update_2 _ _ _ (● Excl' ys ⋅ ◯ Excl' ys)
      with "Hγ● Hγ◯") as "[$$]".
    { by apply auth_update, option_local_update, exclusive_local_update. }
    done.
  Qed.

  Lemma type_weak_try_inc :
    ⊢ typed_function impl_weak_try_inc type_of_weak_try_inc.
  Proof.
    start_function "try_inc" ([[p g] n]) => arg_c local_v local_v2.
    prepare_parameters (p g n).

    (* first read *)
    liRStepUntil @typed_read_end.
    iRename select (own _ _) into "H◯".
    iApply type_read_atomic_int. iIntros (??) "H●".
    iDestruct (auth_agree with "H● H◯") as "%"; subst. iFrame.
    iModIntro.
    
    (* sync before cas *)
    liRStepUntil @typed_cas.
    unfold typed_cas. iIntros.
    unfold typed_val_expr. iIntros (?) "Hcont".
    iRename select (p at{_}ₗ _ ◁ᵥ _)%I into "Hv_cnt".
    iRename select (local_v ◁ᵥ _)%I into "Hv_locv".

    iEval (unfold ty_own_val; simpl) in "Hv_cnt".
    iDestruct "Hv_cnt" as "[_ Hl_cnt]".
    iEval (unfold ty_own; simpl) in "Hl_cnt".
    iDestruct "Hl_cnt" as "[% [Hl_cnt H●]]".
    iDestruct (auth_agree with "H● H◯") as "%"; subst.
    iMod (auth_update g (n+1)%Z with "H● H◯") as "[H● H◯]".

    (* cas *)
    iApply (wp_cas_suc_int with "[Hl_cnt] [Hv_locv] [] [-]").
    1: solve_goal. 2: auto.
    2: { unfold ty_own_val; simpl.
      iDestruct "Hv_locv" as "[_ H]". auto. } auto. auto.
    iNext. repeat liRStep; liShow.

    (* continuation *)
    iApply ("Hcont" $! _ (true @ builtin_boolean))%I.
    { unfold ty_own_val; simpl. auto. }
    do 19 (liRStep; liShow). exists true, (n+1)%Z.
    repeat liRStep; liShow.

    Unshelve. solve_goal.
  Qed.

  Lemma type_weak_inc (global_weak_try_inc : loc) :
    global_weak_try_inc ◁ᵥ global_weak_try_inc @ function_ptr type_of_weak_try_inc -∗
    typed_function (impl_weak_inc global_weak_try_inc) type_of_weak_inc.
  Proof.
    start_function "inc" ([[p g] n]) => arg_c.
    prepare_parameters (p g n).
    split_blocks ((
      <[ "#1" :=
        arg_c ◁ₗ (p @ (&own (counter (g)))) ∗
        own g (◯ Excl' n)
    ]> $
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "inc" "#0".
    - do 36 (liRStep; liShow). exists p, g, n.
      repeat liRStep; liShow. subst. iFrame.
      all: print_typesystem_goal "inc" "#1".
    Unshelve. all: li_unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "inc".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "inc".
  Qed.

  Lemma type_try_inc :
    ⊢ atomic_typed_function ⊤ impl_try_inc type_of_try_inc.
  Proof.
    start_function "try_inc" ([p g]) => arg_c local_v local_v2.

    (* first read. we need to do this manually because
      to prove n+1 <= maxint we should open AU *)
    liRStepUntil @typed_read_end.
    iApply type_read_atomic_int. iIntros (??) "H●".
    iRename select (atomic_update_rc _ _ _ _ _ _) into "AU".
    unfold atomic_update_rc.
    iMod "AU" as (n') "[[% H◯] [Abort _]]".
    iDestruct (auth_agree with "H● H◯") as "%"; subst.
      rename n' into n.
    iMod ("Abort" with "[H◯]") as "AU"; auto. iModIntro.

    (* sync before cas *)
    liRStepUntil @typed_cas.
    unfold typed_cas. iIntros.
    unfold typed_val_expr. iIntros (?) "Hcont".
    iRename select (p at{_}ₗ _ ◁ᵥ _)%I into "Hv_cnt".
    iRename select (local_v ◁ᵥ _)%I into "Hv_locv".

    iEval (unfold ty_own_val; simpl; unfold ty_own; simpl) in "Hv_cnt".
    iDestruct "Hv_cnt" as "[_ [% Inv]]".
    iInv "Inv" as ">[% [Hl_cnt H●]]".
    iMod "AU" as (n') "[[% H◯] [_ Commit]]".
    iDestruct (auth_agree with "H● H◯") as "%"; subst.

    destruct (decide (n = n')).
    - (* suc: commit & update ghost *)
      subst.
      iMod (auth_update g (n'+1)%Z with "H● H◯") as "[H● H◯]".
      (* cas *)
      iApply (wp_cas_suc_int with "[Hl_cnt] [Hv_locv] [] [-]").
      1: solve_goal. 2: auto.
      2: { unfold ty_own_val; simpl.
        iDestruct "Hv_locv" as "[_ Hv_locv]". auto. } auto. auto.
      iNext. repeat liRStep; liShow.
      (* recover inv *)
      iMod ("Commit" $! (true, (n'+1)%Z) with "[H◯]"); simpl; auto.
      iModIntro. iModIntro.
      iRename select (p at{_}ₗ _ ◁ₗ _)%I into "Hl_cnt".
      iSplitL "H● Hl_cnt". {
        iNext. iExists (n'+1)%Z; iFrame.
      }
      (* continuation *)
      iApply ("Hcont" $! _ (true @ builtin_boolean))%I.
      { unfold ty_own_val; simpl. auto. }
      repeat liRStep; liShow.
      iRename select (∀ v4 : val, _)%I into "Hphi".
      iApply "Hphi". iExists (true @ builtin_boolean)%I.
      iSplitR. { unfold ty_own_val; simpl. iExists _. auto. }
      unfold atomic_fn_ret_prop. simpl.
      iIntros. iSplitR; auto. iSplitL; auto.
      unfold counter.
      iRename select (p ◁ₗ{Shr} _)%I into "Hp".
      repeat (unfold ty_own; simpl).
      iDestruct "Hp" as "(H1&H2&H3&H4&H5)". iFrame.
      iSplitL; auto.
    - (* fail: commit, don't update *)
      iApply (wp_cas_fail_int with "[Hl_cnt] [Hv_locv] [] [-]").
      1: solve_goal. 2: auto.
      2: { unfold ty_own_val; simpl.
        iDestruct "Hv_locv" as "[_ Hv_locv]". auto. } auto. auto.
      iNext. repeat liRStep; liShow.
      iMod ("Commit" $! (false, n') with "[H◯]"); simpl; auto. iModIntro. iModIntro.
      iRename select (p at{_}ₗ _ ◁ₗ _)%I into "Hl_cnt".
      iSplitL ("H● Hl_cnt"). {
        iNext. iExists n'. iFrame.
      }
      (* continuation *)
      iApply ("Hcont" $! _ (false @ builtin_boolean))%I.
      { unfold ty_own_val; simpl. auto. }
      repeat liRStep; liShow.
      iRename select (∀ v4 : val, _)%I into "Hphi".
      iApply "Hphi". iExists (false @ builtin_boolean)%I.
      iSplitR. { unfold ty_own_val; simpl. iExists _. auto. }
      unfold atomic_fn_ret_prop. simpl.
      iIntros. iSplitR; auto. iSplitL; auto.
      unfold counter.
      iRename select (p ◁ₗ{Shr} _)%I into "Hp".
      repeat (unfold ty_own; simpl).
      iDestruct "Hp" as "(H1&H2&H3&H4&H5)". iFrame.
      iSplitL; auto.
    
    Unshelve. solve_goal.
  Qed.

  Lemma type_cast_builtin_boolean_boolean_inext b it v T:
    ▷ (∀ v, T v (b @ boolean it)) -∗
    typed_un_op v (v ◁ᵥ b @ builtin_boolean)%I (CastOp (IntOp it)) BoolOp T.
  Proof.
    unfold ty_own_val; simpl.
    iIntros "HT (%n&%Hv&%Hb) %Φ HΦ". move: Hb => /= ?. subst n.
    have [??] := val_of_Z_bool_is_Some None it b.
    iApply wp_cast_bool_int => //. { by apply val_to_bool_iff_val_to_Z. }
    iApply ("HΦ" with "[] HT") => //.
    iExists _. iSplit;[|done]. iPureIntro. by apply: val_to_of_Z.
  Qed.
  
  Lemma type_inc (global_try_inc : loc) :
    global_try_inc ◁ᵥ global_try_inc @ atomic_function_ptr type_of_try_inc ⊤ -∗
    atomic_typed_function ⊤ (impl_inc global_try_inc) type_of_inc.
  Proof.
    start_function "inc" ([p g]) => arg_c.
    prepare_parameters (p g). simpl.
    iIntros "[[Hc _] _] % AU".

    split_blocks ((
      <[ "#1" :=
        arg_c ◁ₗ (p @ (&shr (counter (g)))) ∗
        atomic_update_rc (⊤ ∖ ⊤) ∅
        (λ n : Z, ⌜(n + 1 ≤ max_int i32)%Z⌝ ∗ own g (◯ Excl' n))
        (λ (x1 : Z) (y : ()),
           atfr_atR
             (let
              '() := y in
               mk_atFR void (p ◁ₗ{Shr} counter g)
                 (own g (◯ Excl' (x1 + 1)%Z)))) Φ
        (λ (x : Z) (y : ()) (v : val),
           ∃ ty : type, v ◁ᵥ ty ∗
             atomic_fn_ret_prop
               (let
                '() := y in
                 mk_atFR void (p ◁ₗ{Shr} counter g)
                   (own g (◯ Excl' (x + 1)%Z))) v ty)
    ]> $
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    { repeat liRStep. }
    
    iIntros "[Hargc AU]". repeat liRStep; liShow.
    iRename select (arg_c ◁ₗ _)%I into "Hargc".
    iApply type_call_atfnptr; simpl.
      rewrite (_ : ⊤ ∖ ⊤ = ∅); last set_solver.
      iIntros. iExists (p, g). simpl.
      iSplitR; auto. iSplitR; auto.
    iAuIntro. iMod "AU" as (n) "[[%Hn Pre] AU]".
    unfold atomic_acc. iModIntro. iExists n.
    iSplitL "Pre"; auto.
    iSplit.
    {
      (* abort in try_inc's AU *)
      iIntros "Pre". iFrame. 
      iDestruct "AU" as "[Abort _]".
      iMod ("Abort" with "Pre"). by iModIntro.
    }
    (* commit *)
    iIntros (result) "Pre".
    destruct result. destruct b.
    - (* CAS success *)
      iDestruct "AU" as "[_ Commit]".
      iMod ("Commit" $! () with "[Pre]") as "Cont"; simpl; auto.
      { iDestruct "Pre" as "[Pre %]". by subst. }
      iModIntro.
      iIntros (v0) "Hp". liRStep; liShow.
      iApply type_cast_builtin_boolean_boolean_inext. iNext.
      repeat liRStep; liShow.
      iApply "Cont". iExists void. iSplitR.
      { unfold ty_own_val, VOID; simpl. auto. }
      unfold atomic_fn_ret_prop; simpl. auto.
    - (* CAS fail *)
      iDestruct "AU" as "[Abort _]".
      iMod ("Abort" with "[Pre]") as "Cont"; simpl; auto.
      { iDestruct "Pre" as "[Pre %]". subst. by iFrame. }
      iModIntro.
      iIntros (v0) "Hp". liRStep; liShow.
      iApply type_cast_builtin_boolean_boolean_inext. iNext.
      repeat liRStep; liShow.
  Qed.
End type.
