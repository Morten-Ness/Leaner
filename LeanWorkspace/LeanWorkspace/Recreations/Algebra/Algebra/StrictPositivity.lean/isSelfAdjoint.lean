import Mathlib

variable {A : Type*}

theorem isSelfAdjoint [Semiring A] [PartialOrder A] [StarRing A] [StarOrderedRing A] {a : A}
    (ha : IsStrictlyPositive a) : IsSelfAdjoint a := ha.nonneg.isSelfAdjoint

