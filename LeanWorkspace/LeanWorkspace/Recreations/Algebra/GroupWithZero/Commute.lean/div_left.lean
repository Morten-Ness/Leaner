import Mathlib

open scoped Ring

variable {M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] {a b c : G₀}

theorem div_left (hac : Commute a c) (hbc : Commute b c) : Commute (a / b) c := by
  rw [div_eq_mul_inv]
  exact hac.mul_left Commute.inv_left₀ hbc

