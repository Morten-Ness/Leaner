import Mathlib

variable {R : Type u}

variable [NonAssocSemiring R] [PartialOrder R] [CanonicallyOrderedAdd R]
  [Sub R] [OrderedSub R] [@Std.Total R (· ≤ ·)]

theorem tsub_one_mul [MulRightMono R] [AddLeftReflectLE R] (a b : R) :
    (a - 1) * b = a * b - b := by rw [tsub_mul, one_mul]

