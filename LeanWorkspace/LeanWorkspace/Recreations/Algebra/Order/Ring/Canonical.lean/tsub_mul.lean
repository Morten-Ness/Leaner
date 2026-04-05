import Mathlib

variable {R : Type u}

variable [NonUnitalNonAssocSemiring R] [PartialOrder R] [CanonicallyOrderedAdd R]
  [Sub R] [OrderedSub R] [@Std.Total R (· ≤ ·)]

variable [AddLeftReflectLE R]

theorem tsub_mul [MulRightMono R] (a b c : R) :
    (a - b) * c = a * c - b * c := Contravariant.AddLECancellable.tsub_mul

