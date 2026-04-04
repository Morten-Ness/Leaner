import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P]

variable (P) in

theorem vectorSpan_empty : vectorSpan k (∅ : Set P) = (⊥ : Submodule k V) := by
  rw [vectorSpan_def, vsub_empty, Submodule.span_empty]

