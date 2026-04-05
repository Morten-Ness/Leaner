import Mathlib

variable {R : Type*}

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]

theorem nonneg [Nontrivial R] {t : Set.Ico (0 : R) 1} : 0 ≤ t := t.2.1

