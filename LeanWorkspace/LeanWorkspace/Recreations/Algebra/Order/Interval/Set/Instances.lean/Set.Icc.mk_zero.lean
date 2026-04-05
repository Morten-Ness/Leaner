import Mathlib

variable {R : Type*}

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]

theorem mk_zero (h : (0 : R) ∈ Set.Icc (0 : R) 1) : (⟨0, h⟩ : Set.Icc (0 : R) 1) = 0 := rfl

