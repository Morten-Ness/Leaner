import Mathlib

variable {R : Type*}

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]

theorem le_one {t : Set.Icc (0 : R) 1} : t ≤ 1 := t.2.2

