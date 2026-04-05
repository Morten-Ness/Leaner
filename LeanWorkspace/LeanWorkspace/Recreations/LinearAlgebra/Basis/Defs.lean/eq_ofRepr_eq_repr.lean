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

theorem eq_ofRepr_eq_repr {b₁ b₂ : Module.Basis ι R M} (h : ∀ x i, b₁.repr x i = b₂.repr x i) : b₁ = b₂ := Module.Basis.repr_injective <| by Module.Basis.ext; apply h

