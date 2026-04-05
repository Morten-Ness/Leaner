import Mathlib

variable {R ι : Type*}

variable [Semiring R] [CharP R 2]

theorem two_nsmul (x : R) : 2 • x = 0 := by rw [two_nsmul, CharTwo.add_self_eq_zero]

