import Mathlib

variable {R : Type*}

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]

theorem mk_one (h : (1 : R) ∈ Set.Ioc (0 : R) 1) : (⟨1, h⟩ : Set.Ioc (0 : R) 1) = 1 := rfl

