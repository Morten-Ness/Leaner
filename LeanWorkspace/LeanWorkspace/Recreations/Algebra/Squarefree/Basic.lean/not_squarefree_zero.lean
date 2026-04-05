import Mathlib

variable {R : Type*}

theorem not_squarefree_zero [MonoidWithZero R] [Nontrivial R] : ¬Squarefree (0 : R) := by
  rw [Squarefree, not_forall]
  exact ⟨0, by simp⟩

