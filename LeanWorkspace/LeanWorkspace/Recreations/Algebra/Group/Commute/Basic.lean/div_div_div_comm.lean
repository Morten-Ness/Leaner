import Mathlib

variable {G : Type*}

variable [DivisionMonoid G] {a b c d : G}

theorem div_div_div_comm (hbc : Commute b c) (hbd : Commute b⁻¹ d) (hcd : Commute c⁻¹ d) :
    a / b / (c / d) = a / c / (b / d) := by
  simp_rw [div_eq_mul_inv, mul_inv_rev, Commute.inv_inv, hbd.symm.eq, hcd.symm.eq,
    Commute.inv_inv hbc.mul_mul_mul_comm]

