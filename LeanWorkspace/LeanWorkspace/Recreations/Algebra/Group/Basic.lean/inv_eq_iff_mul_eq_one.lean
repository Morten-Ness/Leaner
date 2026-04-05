import Mathlib

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem inv_eq_iff_mul_eq_one : a⁻¹ = b ↔ a * b = 1 := mul_eq_one_iff_inv_eq.symm

