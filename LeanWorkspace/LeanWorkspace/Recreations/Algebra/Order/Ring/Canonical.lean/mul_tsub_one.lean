import Mathlib

variable {R : Type u}

variable [NonAssocSemiring R] [PartialOrder R] [CanonicallyOrderedAdd R]
  [Sub R] [OrderedSub R] [@Std.Total R (· ≤ ·)]

theorem mul_tsub_one [AddLeftReflectLE R] (a b : R) :
    a * (b - 1) = a * b - a := by rw [mul_tsub, mul_one]

