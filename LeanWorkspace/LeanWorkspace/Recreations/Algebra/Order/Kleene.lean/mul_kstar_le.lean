import Mathlib

variable {α β ι : Type*} {π : ι → Type*}

variable [KleeneAlgebra α] {a b c : α}

theorem mul_kstar_le (hb : b ≤ c) (ha : c * a ≤ c) : b * a∗ ≤ c := by grw [hb, mul_kstar_le_self ha]

