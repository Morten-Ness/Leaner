import Mathlib

variable {α : Type*}

variable [Ring α] [LinearOrder α] [IsOrderedRing α] {n : ℕ} {a b : α}

theorem exists_abs_lt [Nontrivial α] (a : α) : ∃ b > 0, |a| < b := ⟨|a| + 1, lt_of_lt_of_le zero_lt_one <| by simp, lt_add_one |a|⟩

