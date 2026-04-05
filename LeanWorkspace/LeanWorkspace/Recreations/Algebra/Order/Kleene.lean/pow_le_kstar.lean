import Mathlib

variable {α β ι : Type*} {π : ι → Type*}

variable [KleeneAlgebra α] {a b c : α}

theorem pow_le_kstar : ∀ {n : ℕ}, a ^ n ≤ a∗
  | 0 => (pow_zero _).trans_le one_le_kstar
  | n + 1 => by grw [pow_succ', pow_le_kstar, mul_kstar_le_kstar]
