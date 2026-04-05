import Mathlib

section

variable {M : Type*}

variable [DivisionMonoid M] {a b c d : M}

theorem div_eq_div_iff_of_isUnit (hbd : Commute b d) (hb : IsUnit b) (hd : IsUnit d) :
    a / b = c / d ↔ a * d = c * b := by
  rw [← (hb.mul hd).mul_left_inj, ← mul_assoc, hb.div_mul_cancel, ← mul_assoc, hbd.right_comm,
    hd.div_mul_cancel]

end

section

variable {M : Type*}

variable [DivisionMonoid M] {a b c d : M}

theorem inv_mul_eq_inv_mul_iff_of_isUnit (hbd : Commute b d) (hb : IsUnit b) (hd : IsUnit d) :
    b⁻¹ * a = d⁻¹ * c ↔ d * a = b * c := by
  rw [← (hd.mul hb).mul_right_inj, ← mul_assoc, mul_assoc d, hb.mul_inv_cancel, mul_one,
    ← mul_assoc, mul_assoc d, hbd.symm.left_comm, hd.mul_inv_cancel, mul_one]

end

section

variable {M : Type*}

variable [DivisionMonoid M] {a b c d : M}

theorem mul_inv_eq_mul_inv_iff_of_isUnit (hbd : Commute b d) (hb : IsUnit b) (hd : IsUnit d) :
    a * b⁻¹ = c * d⁻¹ ↔ a * d = c * b := by
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, Commute.div_eq_div_iff_of_isUnit hbd hb hd]

end
