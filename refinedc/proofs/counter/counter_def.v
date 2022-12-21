From iris.algebra Require Import excl auth.
From refinedc.typing Require Import typing atomic_int.
From refinedc.project.ex.counter Require Import generated_code.
Set Default Proof Using "Type".

Definition numUR := authR $ optionUR $ exclR ZO.
Class counterG Σ := cG {counter_tokG :> inG Σ numUR;}.
Definition counterΣ : gFunctors := #[GFunctor numUR].
Global Instance subG_counterΣ {Σ} : subG counterΣ Σ → counterG Σ.
Proof. solve_inG. Qed.

Section type.
  Context `{!typeG Σ} `{!counterG Σ}.

  Definition counter (γ : gname) : type :=
    struct struct_counter [atomic_int i32
      (λ n, own γ (● Some (Excl n)) )%I
    ].
End type.
