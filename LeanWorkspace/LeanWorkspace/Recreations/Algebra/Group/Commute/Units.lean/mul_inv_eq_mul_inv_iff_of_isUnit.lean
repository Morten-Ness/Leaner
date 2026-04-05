import Mathlib

variable {M : Type*}

variable [DivisionMonoid M] {a b c d : M}

theorem mul_inv_eq_mul_inv_iff_of_isUnit (hbd : Commute b d) (hb : IsUnit b) (hd : IsUnit d) :
    a * b⁻¹ = c * d⁻¹ ↔ a * d = c * b := by
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, Commute.div_eq_div_iff_of_isUnit hbd hb hd]

