import Mathlib

variable {R : Type*}

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]

theorem mk_zero [Nontrivial R] (h : (0 : R) ∈ Set.Ico (0 : R) 1) : (⟨0, h⟩ : Set.Ico (0 : R) 1) = 0 := rfl

