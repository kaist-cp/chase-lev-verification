From chase_lev Require Import atomic.
From iris.heap_lang Require Import proofmode notation.
From iris.prelude Require Import options.

(** A general logically atomic interface for Chase-Lev deques. *)
Record atomic_deque {Σ} `{!heapGS Σ} := AtomicDEQUE {
  (* -- operations -- *)
  new_deque : val;
  push : val;
  pop : val;
  steal : val;
  (* -- other data -- *)
  name : Type;
  name_eqdec : EqDecision name;
  name_countable : Countable name;
  (* -- predicates -- *)
  is_deque (N : namespace) (γ : name) (q : val) : iProp Σ;
  own_deque (N : namespace) (γ : name) (q : val) : iProp Σ;
  deque_content (γ : name) (ls : list val) : iProp Σ;
  (* -- predicate properties -- *)
  is_deque_persistent N γ p : Persistent (is_deque N γ p);
  deque_content_timeless γ ls : Timeless (deque_content γ ls);
  deque_content_exclusive γ ls1 ls2 :
    deque_content γ ls1 -∗ deque_content γ ls2 -∗ False;
  (* -- operation specs -- *)
  new_deque_spec N n :
    0 < n →
    {{{ True }}}
      new_deque #n
    {{{ γ p, RET p;
      is_deque N γ p ∗ deque_content γ [] ∗ own_deque N γ p
    }}};
  push_spec N γ p (v : val) :
    is_deque N γ p -∗ own_deque N γ p -∗
    <<< ∀∀ l : list val, deque_content γ l >>>
      push p v @ ↑N
    <<< deque_content γ (l ++ [v]),
      RET #(), own_deque N γ p >>>;
  pop_spec N γ p :
    is_deque N γ p -∗ own_deque N γ p -∗
    <<< ∀∀ l : list val, deque_content γ l >>>
      pop p @ ↑N
    <<< ∃∃ (l' : list val) (ov : val),
      deque_content γ l' ∗
      (⌜ov = NONEV ∧ l = l'⌝ ∨
        ∃ v, ⌜ov = SOMEV v ∧ l = l' ++ [v]⌝),
      RET ov, own_deque N γ p >>>;
  steal_spec N γ p :
    is_deque N γ p -∗
    <<< ∀∀ l : list val, deque_content γ l >>>
      steal p @ ↑N
    <<< ∃∃ (l' : list val) (ov : val),
      deque_content γ l' ∗
      (⌜ov = NONEV ∧ l = l'⌝ ∨
        ∃ v, ⌜ov = SOMEV v ∧ l = [v] ++ l'⌝),
    RET ov >>>;
}.
Global Arguments atomic_deque _ {_}.

Global Existing Instances is_deque_persistent deque_content_timeless.
