import Mathlib

variable {R : Type*}

theorem squarefree_natCast {n : ℕ} : Squarefree (n : ℤ) ↔ Squarefree n := by
  rw [← Int.squarefree_natAbs, natAbs_natCast]

