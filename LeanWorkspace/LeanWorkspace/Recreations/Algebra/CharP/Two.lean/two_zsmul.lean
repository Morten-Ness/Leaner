import Mathlib

variable {R ι : Type*}

variable [Ring R] [CharP R 2]

theorem two_zsmul (x : R) : (2 : ℤ) • x = 0 := by
  rw [two_zsmul, CharTwo.add_self_eq_zero]

