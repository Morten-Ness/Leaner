import Mathlib

variable {R : Type*}

theorem mul_eq_zero_of_anticommute {a b : R} [NonUnitalSemiring R] [IsAddTorsionFree R]
    (ha : IsIdempotentElem a) (hab : a * b + b * a = 0) : a * b = 0 := by
  have h : a * b * a = 0 := by
    rw [← nsmul_right_inj ((Nat.zero_ne_add_one 1).symm), nsmul_zero]
    have : a * (a * b + b * a) * a = 0 := by rw [hab, mul_zero, zero_mul]
    simp_rw [mul_add, add_mul, mul_assoc, ha.eq, ← mul_assoc, ha.eq, ← two_nsmul] at this
    exact this
  suffices a * a * b + a * b * a = 0 by rwa [h, add_zero, ha.eq] at this
  rw [mul_assoc, mul_assoc, ← mul_add, hab, mul_zero]

