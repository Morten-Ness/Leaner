import Mathlib

variable {R : Type*}

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]

variable {β : Type*} [Ring β] [PartialOrder β] [IsOrderedRing β]

theorem one_minus_pos (x : Set.Ioo (0 : β) 1) : 0 < 1 - (x : β) := by simpa using x.2.2

