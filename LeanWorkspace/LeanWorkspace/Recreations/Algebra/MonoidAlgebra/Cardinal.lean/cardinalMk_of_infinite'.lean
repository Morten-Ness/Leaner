import Mathlib

variable (R M : Type u) (M' : Type v) [Semiring R]

theorem cardinalMk_of_infinite' [Nonempty M] [Infinite R] : #R[M] = max #R #M := by simp

