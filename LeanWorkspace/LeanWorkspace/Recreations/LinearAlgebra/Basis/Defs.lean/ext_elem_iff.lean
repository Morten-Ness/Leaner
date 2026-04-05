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

theorem ext_elem_iff {x y : M} : x = y ↔ ∀ i, b.repr x i = b.repr y i := by
  simp only [← DFunLike.ext_iff, EmbeddingLike.apply_eq_iff_eq]

alias ⟨_, ext_elem⟩ := ext_elem_iff

