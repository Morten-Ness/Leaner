import Mathlib

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem eq_inv_iff_mul_eq_one : a = b⁻¹ ↔ a * b = 1 := mul_eq_one_iff_eq_inv.symm

