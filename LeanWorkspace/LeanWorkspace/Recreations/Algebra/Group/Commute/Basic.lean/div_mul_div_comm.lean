import Mathlib

variable {G : Type*}

variable [DivisionMonoid G] {a b c d : G}

theorem div_mul_div_comm (hbd : Commute b d) (hbc : Commute b⁻¹ c) :
    a / b * (c / d) = a * c / (b * d) := by
  simp_rw [div_eq_mul_inv, mul_inv_rev, Commute.inv_inv hbd.symm.eq, hbc.mul_mul_mul_comm]

