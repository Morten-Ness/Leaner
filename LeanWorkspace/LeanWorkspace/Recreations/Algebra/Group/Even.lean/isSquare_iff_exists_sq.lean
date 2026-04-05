import Mathlib

variable {F α β : Type*}

variable [Monoid α] {n : ℕ} {a : α}

theorem isSquare_iff_exists_sq (a : α) : IsSquare a ↔ ∃ r, a = r ^ 2 := by simp [IsSquare, pow_two]

