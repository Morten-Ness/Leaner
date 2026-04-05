import Mathlib

variable {R : Type u}

variable [NonUnitalNonAssocSemiring R] [PartialOrder R] [CanonicallyOrderedAdd R]
  [Sub R] [OrderedSub R] [@Std.Total R (· ≤ ·)]

variable [AddLeftReflectLE R]

theorem mul_tsub (a b c : R) : a * (b - c) = a * b - a * c := Contravariant.AddLECancellable.mul_tsub

