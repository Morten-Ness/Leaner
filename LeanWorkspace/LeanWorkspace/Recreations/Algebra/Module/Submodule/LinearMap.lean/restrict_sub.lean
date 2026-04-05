import Mathlib

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}

variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable {ι : Type*}

variable [Semiring R] [Semiring R₂] [Semiring R₃]

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R M₁] [Module R₂ M₂] [Module R₃ M₃]

variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

variable (f : M →ₛₗ[σ₁₂] M₂) (g : M₂ →ₛₗ[σ₂₃] M₃)

theorem restrict_sub {R M M₁ : Type*}
    [Ring R] [AddCommGroup M] [AddCommGroup M₁] [Module R M] [Module R M₁]
    {p : Submodule R M} {q : Submodule R M₁} {f g : M →ₗ[R] M₁}
    (hf : MapsTo f p q) (hg : MapsTo g p q)
    (hfg : MapsTo (f - g) p q := fun _ hx ↦ q.sub_mem (hf hx) (hg hx)) :
    f.restrict hf - g.restrict hg = (f - g).restrict hfg := by
  ext; simp

