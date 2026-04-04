import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P]

variable (P) in

theorem vectorSpan_of_subsingleton {s : Set P} (h : s.Subsingleton) : vectorSpan k s = ⊥ := by
  rcases h.eq_empty_or_singleton with rfl | ⟨p, rfl⟩ <;> simp

