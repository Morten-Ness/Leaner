import Mathlib

variable {R : Type u}

variable [NonUnitalNonAssocSemiring R] [PartialOrder R] [CanonicallyOrderedAdd R]
  [Sub R] [OrderedSub R] [@Std.Total R (· ≤ ·)]

theorem tsub_mul [MulRightMono R] {a b c : R}
    (h : AddLECancellable (b * c)) : (a - b) * c = a * c - b * c := by
  obtain (hab | hba) := total_of (· ≤ ·) a b
  · rw [tsub_eq_zero_iff_le.2 hab, zero_mul, tsub_eq_zero_iff_le.2 (mul_le_mul_left hab c)]
  · apply h.eq_tsub_of_add_eq
    rw [← add_mul, tsub_add_cancel_of_le hba]

