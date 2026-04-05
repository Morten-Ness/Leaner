import Mathlib

variable {R : Type*} {R₂ : Type*} {R₃ : Type*}

variable {K : Type*}

variable {M : Type*} {M₂ : Type*} {M₃ : Type*}

variable {V : Type*} {V₂ : Type*}

variable [Semiring R] [Semiring R₂] [AddCommMonoid M] [AddCommMonoid M₂]

variable [Module R M] [Module R₂ M₂]

variable (p : Submodule R M)

variable {τ₁₂ : R →+* R₂}

theorem restrictScalars_map [SMul R R₂] [Module R₂ M] [Module R M₂] [IsScalarTower R R₂ M]
    [IsScalarTower R R₂ M₂] (f : M →ₗ[R₂] M₂) (M' : Submodule R₂ M) :
    (M'.map f).restrictScalars R = (M'.restrictScalars R).map (f.restrictScalars R) := rfl

