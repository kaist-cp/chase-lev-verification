From chase_lev Require Import atomic.
From chase_lev.circular2 Require Import helpers.
From iris.heap_lang Require Import proofmode notation.
From iris.prelude Require Import options.

(** A general logically atomic interface for Circular Arrays. *)
Record atomic_circle {Σ} `{!heapGS Σ} := AtomicCIRCLE {
  (* -- operations -- *)
  new_circle : val;
  get_circle : val;
  (*set_circle : val;*)
  (*grow_circle : val;*)
  (* -- other data -- *)
  name : Type;
  name_eqdec : EqDecision name;
  name_countable : Countable name;
  (* -- predicates -- *)
  is_circle (N : namespace) (γ : name) (ca : val) : iProp Σ;
  own_circle (N : namespace) (ca : val) : iProp Σ;
  circle_content (γ : name) (ls : list val) : iProp Σ;
  (* -- predicate properties -- *)
  is_circle_persistent N γ ca : Persistent (is_circle N γ ca);
  circle_content_timeless γ ls : Timeless (circle_content γ ls);
  circle_content_exclusive γ ls1 ls2 :
    circle_content γ ls1 -∗ circle_content γ ls2 -∗ False;
  (* -- operation specs -- *)
  new_circle_spec N n :
    0 < n →
    {{{ True }}}
      new_circle #n
    {{{ γ ca l, RET ca;
      ⌜length l = n⌝ ∗
      is_circle N γ ca ∗ circle_content γ l ∗ own_circle N ca
    }}};
  get_circle_spec N γ ca (i : nat) :
    is_circle N γ ca -∗
    <<< ∀∀ l : list val, circle_content γ l >>>
      get_circle ca #i @ ↑N
    <<< ∃∃ v,
      ⌜mod_get l i = Some v⌝ ∗
      circle_content γ l,
    RET v >>>;
(*
  pop_spec N γ sz q :
    is_circle N γ sz q -∗ own_circle N γ sz q -∗
    <<< ∀∀ l : list val, circle_content γ l >>>
      pop q @ ↑N
    <<< ∃∃ (l' : list val) (ov : val),
        circle_content γ l' ∗
        match ov with
        | NONEV => ⌜l = l'⌝
        | SOMEV v => ⌜l = l' ++ [v]⌝
        | _ => False
        end,
      RET ov, own_circle N γ sz q >>>;
  steal_spec N γ sz q :
    is_circle N γ sz q -∗
    <<< ∀∀ l : list val, circle_content γ l >>>
      steal q @ ↑N
    <<< ∃∃ (l' : list val) (ov : val),
        circle_content γ l' ∗
        match ov with
        | NONEV => ⌜l = l'⌝
        | SOMEV v => ⌜l = [v] ++ l'⌝
        | _ => False
        end,
      RET ov >>>;
*)
}.
Global Arguments atomic_circle _ {_}.

Global Existing Instances is_circle_persistent circle_content_timeless.
