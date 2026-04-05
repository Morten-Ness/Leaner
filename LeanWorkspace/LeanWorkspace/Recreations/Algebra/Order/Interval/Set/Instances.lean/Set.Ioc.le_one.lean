import Mathlib

variable {R : Type*}

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]

theorem le_one {t : Set.Ioc (0 : R) 1} : t ≤ 1 := t.2.2

