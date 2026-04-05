import Mathlib

variable (R : Type u) [Ring R]

variable {X₁ X₂ : Type v}

variable {M N : ModuleCat.{v} R}

theorem isZero_of_iff_subsingleton {M : Type*} [AddCommGroup M] [Module R M] :
    IsZero (of R M) ↔ Subsingleton M := ModuleCat.isZero_iff_subsingleton

