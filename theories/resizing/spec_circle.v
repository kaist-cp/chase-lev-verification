From chase_lev Require Import atomic.
From chase_lev.resizing Require Import helpers.
From iris.heap_lang Require Import proofmode notation.
From iris.prelude Require Import options.

(** A general logically atomic interface for Circular Arrays. *)
Record atomic_circle {Σ} `{!heapGS Σ} := AtomicCIRCLE {
  (* -- operations -- *)
  new_circle : val;
  size_circle : val;
  get_circle : val;
  set_circle : val;
  grow_circle : val;
  (* -- other data -- *)
  name : Type;
  name_eqdec : EqDecision name;
  name_countable : Countable name;
  (* -- predicates -- *)
  is_circle (N : namespace) (γ : name) (ca : val) : iProp Σ;
  circle_content (γ : name) (ls : list val) : iProp Σ;
  persistent_circle (ca : val) (ls : list val) : iProp Σ;
  own_circle (ca : val) (l : list val) : iProp Σ;
  (* -- predicate properties & specs -- *)
  circle_content_exclusive γ ls1 ls2 :
    circle_content γ ls1 -∗ circle_content γ ls2 -∗ False;
  circle_content_timeless γ ls : Timeless (circle_content γ ls);
  is_circle_persistent N γ ca : Persistent (is_circle N γ ca);
  persistent_circle_persistent ca l : Persistent (persistent_circle ca l);
  own_circle_persist ca l : own_circle ca l ==∗ persistent_circle ca l;
  (* -- operation specs -- *)
  new_circle_spec N n :
    0 < n →
    {{{ True }}}
      new_circle #n
    {{{ γ ca l, RET ca;
      ⌜length l = n⌝ ∗
      is_circle N γ ca ∗ circle_content γ l ∗ own_circle ca l
    }}};
  size_circle_spec N γ ca (i : nat) :
    is_circle N γ ca -∗
    <<< ∀∀ (l : list val), circle_content γ l >>>
      size_circle ca @ ↑N
    <<< circle_content γ l, RET #(length l) >>>;
  get_circle_spec N γ ca (i : nat) :
    is_circle N γ ca -∗
    <<< ∀∀ (l : list val) (current : bool),
      if current then circle_content γ l else persistent_circle ca l >>>
      get_circle ca #i @ ↑N
    <<< ∃∃ v,
      ⌜mod_get l i = Some v⌝ ∗
      if current then circle_content γ l else persistent_circle ca l,
    RET v >>>;
  set_circle_spec N γ ca l (i : nat) (v : val) :
    is_circle N γ ca -∗ own_circle ca l -∗
    <<< circle_content γ l >>>
      set_circle ca #i v @ ↑N
    <<< circle_content γ (mod_set l i v),
    RET #(), own_circle ca (mod_set l i v) >>>;
  grow_circle_spec N γ ca l (t b : nat) :
    0 < length l →
    t ≤ b < t + length l →
    is_circle N γ ca -∗ own_circle ca l -∗
    <<< ∀∀ (_ : ()), circle_content γ l >>>
      grow_circle ca #t #b @ ↑N
    <<< ∃∃ γ' (ca' : val) (l' : list val),
      ⌜length l < length l'⌝ ∗
      ⌜circ_slice l t b = circ_slice l' t b⌝ ∗
      is_circle N γ' ca' ∗ circle_content γ l ∗ circle_content γ' l',
    RET ca', own_circle ca l ∗ own_circle ca' l' >>>;
}.
Global Arguments atomic_circle _ {_}.

Global Existing Instances is_circle_persistent circle_content_timeless.
