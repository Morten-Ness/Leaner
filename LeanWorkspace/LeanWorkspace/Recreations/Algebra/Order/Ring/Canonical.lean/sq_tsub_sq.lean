import Mathlib

variable {R : Type u}

variable [CommSemiring R] [PartialOrder R] [CanonicallyOrderedAdd R]
  [Sub R] [OrderedSub R] [@Std.Total R (· ≤ ·)] [AddLeftReflectLE R]

theorem sq_tsub_sq (a b : R) : a ^ 2 - b ^ 2 = (a + b) * (a - b) := by
  rw [sq, sq, mul_self_tsub_mul_self]

