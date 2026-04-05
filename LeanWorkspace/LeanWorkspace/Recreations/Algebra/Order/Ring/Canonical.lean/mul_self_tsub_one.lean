import Mathlib

variable {R : Type u}

variable [CommSemiring R] [PartialOrder R] [CanonicallyOrderedAdd R]
  [Sub R] [OrderedSub R] [@Std.Total R (· ≤ ·)] [AddLeftReflectLE R]

theorem mul_self_tsub_one (a : R) : a * a - 1 = (a + 1) * (a - 1) := by
  rw [← mul_self_tsub_mul_self, mul_one]

