import Mathlib

variable (R M : Type u) (M' : Type v) [Semiring R]

theorem cardinalMk_of_fintype [Fintype M] : #R[M] = #R ^ card M := by simp

