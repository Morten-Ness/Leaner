import Mathlib

variable {M : Type*}

variable [DivisionMonoid M] {a b c d : M}

theorem div_eq_div_iff_of_isUnit (hbd : Commute b d) (hb : IsUnit b) (hd : IsUnit d) :
    a / b = c / d ↔ a * d = c * b := by
  rw [← (hb.mul hd).mul_left_inj, ← mul_assoc, hb.div_mul_cancel, ← mul_assoc, hbd.right_comm,
    hd.div_mul_cancel]

