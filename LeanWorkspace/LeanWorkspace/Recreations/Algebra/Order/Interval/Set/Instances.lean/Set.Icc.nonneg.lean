import Mathlib

variable {R : Type*}

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]

theorem nonneg {t : Set.Icc (0 : R) 1} : 0 ≤ t := t.2.1

