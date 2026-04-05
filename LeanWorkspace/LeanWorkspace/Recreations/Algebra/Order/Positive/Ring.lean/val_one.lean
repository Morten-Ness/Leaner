import Mathlib

variable {M R : Type*}

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]

theorem val_one : ((1 : { x : R // 0 < x }) : R) = 1 := rfl

