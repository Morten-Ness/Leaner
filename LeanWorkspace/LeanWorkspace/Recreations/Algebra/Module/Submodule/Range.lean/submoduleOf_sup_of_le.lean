import Mathlib

variable {R : Type*} {R₂ : Type*} {R₃ : Type*}

variable {K : Type*}

variable {M : Type*} {M₂ : Type*} {M₃ : Type*}

variable {V : Type*} {V₂ : Type*}

variable [Semiring R] [Semiring R₂] [AddCommMonoid M] [AddCommMonoid M₂]

variable [Module R M] [Module R₂ M₂]

variable (p : Submodule R M)

variable {τ₁₂ : R →+* R₂}

theorem submoduleOf_sup_of_le {N₁ N₂ N : Submodule R M} (h₁ : N₁ ≤ N) (h₂ : N₂ ≤ N) :
    (N₁ ⊔ N₂).submoduleOf N = N₁.submoduleOf N ⊔ N₂.submoduleOf N := by
  apply Submodule.map_injective_of_injective N.subtype_injective
  simp only [submoduleOf, map_comap_eq]
  simp_all

