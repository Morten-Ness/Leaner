import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] {a b c : G₀} {m n : ℕ}

theorem div_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) : a / b ≠ 0 := by
  rw [div_eq_mul_inv]
  exact mul_ne_zero ha (inv_ne_zero hb)

