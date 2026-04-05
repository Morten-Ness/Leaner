import Mathlib

variable {R : Type*}

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]

variable {β : Type*} [Ring β] [PartialOrder β] [IsOrderedRing β]

theorem one_sub_nonneg (x : Set.Icc (0 : β) 1) : 0 ≤ 1 - (x : β) := by simpa using x.2.2

