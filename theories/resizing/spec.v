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
  is_deque (N : namespace) (γ : name) (sz : nat) (q : val) : iProp Σ;
  own_deque (N : namespace) (γ : name) (sz : nat) (q : val) : iProp Σ;
  deque_content (γ : name) (ls : list val) : iProp Σ;
  (* -- predicate properties -- *)
  is_deque_persistent N γ sz q : Persistent (is_deque N γ sz q);
  deque_content_timeless γ ls : Timeless (deque_content γ ls);
  deque_content_exclusive γ ls1 ls2 :
    deque_content γ ls1 -∗ deque_content γ ls2 -∗ False;
  (* -- operation specs -- *)
  new_deque_spec N sz :
    0 < sz →
    {{{ True }}}
      new_deque #sz
    {{{ γ q, RET q;
      is_deque N γ sz q ∗ deque_content γ [] ∗ own_deque N γ sz q
    }}};
  push_spec N γ sz q (v : val) :
    is_deque N γ sz q -∗ own_deque N γ sz q -∗
    <<< ∀∀ l : list val, deque_content γ l >>>
      push q v @ ↑N
    <<< deque_content γ (l ++ [v]),
      RET #(), own_deque N γ sz q >>>;
  pop_spec N γ sz q :
    is_deque N γ sz q -∗ own_deque N γ sz q -∗
    <<< ∀∀ l : list val, deque_content γ l >>>
      pop q @ ↑N
    <<< ∃∃ (l' : list val) (ov : val),
        deque_content γ l' ∗
        match ov with
        | NONEV => ⌜l = l'⌝
        | SOMEV v => ⌜l = l' ++ [v]⌝
        | _ => False
        end,
      RET ov, own_deque N γ sz q >>>;
  steal_spec N γ sz q :
    is_deque N γ sz q -∗
    <<< ∀∀ l : list val, deque_content γ l >>>
      steal q @ ↑N
    <<< ∃∃ (l' : list val) (ov : val),
        deque_content γ l' ∗
        match ov with
        | NONEV => ⌜l = l'⌝
        | SOMEV v => ⌜l = [v] ++ l'⌝
        | _ => False
        end,
      RET ov >>>;
}.
Global Arguments atomic_deque _ {_}.

Global Existing Instances is_deque_persistent deque_content_timeless.
