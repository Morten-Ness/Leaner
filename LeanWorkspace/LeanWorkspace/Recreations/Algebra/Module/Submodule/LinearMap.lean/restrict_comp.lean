import Mathlib

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}

variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable {ι : Type*}

variable [Semiring R] [Semiring R₂] [Semiring R₃]

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R M₁] [Module R₂ M₂] [Module R₃ M₃]

variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

variable (f : M →ₛₗ[σ₁₂] M₂) (g : M₂ →ₛₗ[σ₂₃] M₃)

theorem restrict_comp
    {M₂ M₃ : Type*} [AddCommMonoid M₂] [AddCommMonoid M₃] [Module R M₂] [Module R M₃]
    {p : Submodule R M} {p₂ : Submodule R M₂} {p₃ : Submodule R M₃}
    {f : M →ₗ[R] M₂} {g : M₂ →ₗ[R] M₃}
    (hf : MapsTo f p p₂) (hg : MapsTo g p₂ p₃) (hfg : MapsTo (g ∘ₗ f) p p₃ := hg.comp hf) :
    (g ∘ₗ f).restrict hfg = (g.restrict hg) ∘ₗ (f.restrict hf) :=
  rfl

-- TODO Consider defining `Algebra R (p.compatibleMaps p)`, `AlgHom` version of `LinearMap.restrict`

