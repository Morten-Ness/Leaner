import Mathlib

variable {R : Type*}

theorem add [NonUnitalNonAssocSemiring R]
    {a b : R} (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (hab : a * b + b * a = 0) : IsIdempotentElem (a + b) := by
  simp_rw [IsIdempotentElem, mul_add, add_mul, ha.eq, hb.eq, add_add_add_comm, ← add_assoc,
    add_assoc a, hab, zero_add]

