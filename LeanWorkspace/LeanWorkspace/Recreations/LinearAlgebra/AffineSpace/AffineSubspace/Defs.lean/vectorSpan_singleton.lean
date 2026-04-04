import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P]

variable (P) in

theorem vectorSpan_singleton (p : P) : vectorSpan k ({p} : Set P) = ⊥ := by simp [vectorSpan_def]

