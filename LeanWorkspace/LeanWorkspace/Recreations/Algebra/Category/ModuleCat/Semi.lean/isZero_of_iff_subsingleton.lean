import Mathlib

variable (R : Type u) [Semiring R]

variable {X₁ X₂ : Type v}

variable {M N : SemimoduleCat.{v} R}

theorem isZero_of_iff_subsingleton {M : Type*} [AddCommMonoid M] [Module R M] :
    IsZero (of R M) ↔ Subsingleton M := SemimoduleCat.isZero_iff_subsingleton

