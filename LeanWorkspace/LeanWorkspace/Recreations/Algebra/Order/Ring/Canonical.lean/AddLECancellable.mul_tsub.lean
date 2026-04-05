import Mathlib

variable {R : Type u}

variable [NonUnitalNonAssocSemiring R] [PartialOrder R] [CanonicallyOrderedAdd R]
  [Sub R] [OrderedSub R] [@Std.Total R (· ≤ ·)]

theorem mul_tsub {a b c : R}
    (h : AddLECancellable (a * c)) : a * (b - c) = a * b - a * c := by
  obtain (hbc | hcb) := total_of (· ≤ ·) b c
  · rw [tsub_eq_zero_iff_le.2 hbc, mul_zero, tsub_eq_zero_iff_le.2 (mul_le_mul_right hbc a)]
  · apply h.eq_tsub_of_add_eq
    rw [← mul_add, tsub_add_cancel_of_le hcb]

