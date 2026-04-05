import Mathlib

variable {R : Type*}

theorem sub [NonUnitalNonAssocRing R] {a b : R} (ha : IsIdempotentElem a)
    (hb : IsIdempotentElem b) (hab : a * b = a) (hba : b * a = a) : IsIdempotentElem (b - a) := by
  simp_rw [IsIdempotentElem, sub_mul, mul_sub, hab, hba, ha.eq, hb.eq, sub_self, sub_zero]

