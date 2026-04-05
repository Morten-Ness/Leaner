import Mathlib

variable {R : Type*} {R₂ : Type*} {R₃ : Type*}

variable {K : Type*}

variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable {V : Type*} {V₂ : Type*}

variable [Semiring R] [Semiring R₂] [Semiring R₃]

variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]

variable {τ₁₂ : R →+* R₂} {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃}

variable [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃]

theorem exists_ne_zero_of_sSup_eq_top {f : M →ₛₗ[τ₁₂] M₂} (h : f ≠ 0) (s : Set (Submodule R M))
    (hs : sSup s = ⊤) : ∃ m ∈ s, f ∘ₛₗ m.subtype ≠ 0 := by
  contrapose! h
  simp_rw [← LinearMap.ker_eq_top, eq_top_iff, ← hs, sSup_le_iff, LinearMap.le_ker_iff_comp_subtype_eq_zero]
  exact h

