FAIL
import Mathlib

variable {M : Type*}

variable [DivisionMonoid M] {a b c d : M}

theorem inv_mul_eq_inv_mul_iff_of_isUnit (hbd : Commute b d) (hb : IsUnit b) (hd : IsUnit d) :
    b⁻¹ * a = d⁻¹ * c ↔ d * a = b * c := by
  rw [← inv_eq_iff_eq_inv]
  exact divp_eq_divp_iff_of_isUnit hbd hb hd
