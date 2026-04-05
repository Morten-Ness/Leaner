import Mathlib

variable {R : Type*}

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]

variable {β : Type*} [Ring β] [PartialOrder β] [IsOrderedRing β]

theorem one_minus_lt_one (x : Set.Ioo (0 : β) 1) : 1 - (x : β) < 1 := by simpa using x.2.1

