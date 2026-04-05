import Mathlib

variable {R : Type*}

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]

variable {β : Type*} [Ring β] [PartialOrder β] [IsOrderedRing β]

theorem one_sub_le_one (x : Set.Icc (0 : β) 1) : 1 - (x : β) ≤ 1 := by simpa using x.2.1

