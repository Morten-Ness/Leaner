import Mathlib

variable {R : Type u}

variable [CommSemiring R] [PartialOrder R] [CanonicallyOrderedAdd R]
  [Sub R] [OrderedSub R] [@Std.Total R (· ≤ ·)] [AddLeftReflectLE R]

theorem mul_self_tsub_mul_self (a b : R) :
    a * a - b * b = (a + b) * (a - b) := by
  rw [mul_tsub, add_mul, add_mul, tsub_add_eq_tsub_tsub, mul_comm b a, add_tsub_cancel_right]

