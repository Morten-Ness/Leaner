import Mathlib

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {K : Type*}

variable {M : Type*} {M' M'' : Type*} {V : Type u} {V' : Type*}

variable [Semiring R]

variable [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

variable {ι R M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable (b : Basis ι R M)

variable {R₁ : Type*} [Semiring R₁] {σ : R →+* R₁} {σ' : R₁ →+* R}

variable [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]

variable {M₁ : Type*} [AddCommMonoid M₁] [Module R₁ M₁]

theorem repr_eq_iff' {b : Module.Basis ι R M} {f : M ≃ₗ[R] ι →₀ R} :
    b.repr = f ↔ ∀ i, f (b i) = Finsupp.single i 1 := ⟨fun h i => h ▸ Module.Basis.repr_self b i, fun h => Module.Basis.ext' b fun i => (Module.Basis.repr_self b i).trans (h i).symm⟩

