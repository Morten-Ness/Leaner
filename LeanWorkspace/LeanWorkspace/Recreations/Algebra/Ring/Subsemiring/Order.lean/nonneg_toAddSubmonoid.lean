import Mathlib

variable {R : Type*}

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]

theorem nonneg_toAddSubmonoid : (Subsemiring.nonneg R).toAddSubmonoid = AddSubmonoid.nonneg R := rfl

