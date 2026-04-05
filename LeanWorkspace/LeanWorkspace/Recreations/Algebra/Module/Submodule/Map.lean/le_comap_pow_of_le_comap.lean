import Mathlib

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}

variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable [Semiring R] [Semiring R₂] [Semiring R₃]

variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]

variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃}

variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

variable (p p' : Submodule R M) (q q' : Submodule R₂ M₂)

variable {x : M}

variable {σ₂₁ : R₂ →+* R} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]

theorem le_comap_pow_of_le_comap (p : Submodule R M) {f : M →ₗ[R] M}
    (h : p ≤ p.comap f) (k : ℕ) : p ≤ p.comap (f ^ k) := by
  induction k with
  | zero => simp [Module.End.one_eq_id]
  | succ k ih => simp [Module.End.iterate_succ, Submodule.comap_comp, h.trans (Submodule.comap_mono ih)]

