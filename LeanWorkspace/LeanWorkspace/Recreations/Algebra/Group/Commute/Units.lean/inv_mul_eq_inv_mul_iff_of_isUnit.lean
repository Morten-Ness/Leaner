import Mathlib

variable {M : Type*}

variable [DivisionMonoid M] {a b c d : M}

theorem inv_mul_eq_inv_mul_iff_of_isUnit (hbd : Commute b d) (hb : IsUnit b) (hd : IsUnit d) :
    b⁻¹ * a = d⁻¹ * c ↔ d * a = b * c := by
  rw [← (hd.mul hb).mul_right_inj, ← mul_assoc, mul_assoc d, hb.mul_inv_cancel, mul_one,
    ← mul_assoc, mul_assoc d, hbd.symm.left_comm, hd.mul_inv_cancel, mul_one]

