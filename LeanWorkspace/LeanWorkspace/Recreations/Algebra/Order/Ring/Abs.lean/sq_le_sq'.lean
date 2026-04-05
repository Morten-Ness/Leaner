import Mathlib

variable {α : Type*}

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {n : ℕ} {a b : α}

theorem sq_le_sq' (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 := sq_le_sq.2 (le_trans (abs_le.mpr ⟨h1, h2⟩) (le_abs_self _))

