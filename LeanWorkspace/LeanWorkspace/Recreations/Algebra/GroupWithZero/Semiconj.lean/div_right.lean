import Mathlib

variable {G₀ : Type*}

variable [GroupWithZero G₀] {a x y x' y' : G₀}

theorem div_right (h : SemiconjBy a x y) (h' : SemiconjBy a x' y') :
    SemiconjBy a (x / x') (y / y') := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact h.mul_right SemiconjBy.inv_right₀ h'

