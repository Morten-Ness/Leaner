import Mathlib

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

variable (R : Type*) [CommSemiring R]

variable (A : Type*) [Semiring A] [Algebra R A]

variable (M : Type*) [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

theorem Module.End.injective_of_surjective_fin [IsStablyFiniteRing A] {n}
    {f : Module.End A (Fin n → A)} (hf : Function.Surjective f) : Function.Injective f := isStablyFiniteRing_iff_injective_of_surjective.mp ‹_› n f hf

