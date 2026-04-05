import Mathlib

open scoped NNRat

variable {R A : Type*}

variable [Ring R] [PartialOrder R] [StarRing R] [StarOrderedRing R] {p : R}

theorem mem_Icc (hp : IsStarProjection p) : p ∈ Set.Icc (0 : R) 1 := by
  simp only [Set.mem_Icc, hp.nonneg, IsStarProjection.le_one hp, and_self]

