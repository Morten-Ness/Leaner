import Mathlib

variable {R : Type*}

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]

theorem mk_one (h : (1 : R) ∈ Set.Icc (0 : R) 1) : (⟨1, h⟩ : Set.Icc (0 : R) 1) = 1 := rfl

