import Mathlib

variable {R R₁ R₂ R₃ S S₃ T M M₁ M₂ M₃ N₂ N₃ : Type*}

variable (F : Type*)

variable [Semiring R] [Semiring S]

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R M₂] [Module S M₃]

variable {σ : R →+* S}

variable {F} (f : F) [FunLike F M M₃] [SemilinearMapClass F σ M M₃]

theorem map_smul_inv {σ' : S →+* R} [RingHomInvPair σ σ'] (c : S) (x : M) :
    c • f x = f (σ' c • x) := by simp [map_smulₛₗ _]

