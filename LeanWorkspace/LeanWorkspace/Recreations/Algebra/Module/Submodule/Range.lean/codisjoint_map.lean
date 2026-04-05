import Mathlib

variable {R : Type*} {R₂ : Type*} {R₃ : Type*}

variable {K : Type*}

variable {M : Type*} {M₂ : Type*} {M₃ : Type*}

variable {V : Type*} {V₂ : Type*}

variable [Semiring R] [Semiring R₂] [AddCommMonoid M] [AddCommMonoid M₂]

variable [Module R M] [Module R₂ M₂]

variable (p : Submodule R M)

variable {τ₁₂ : R →+* R₂}

theorem codisjoint_map [RingHomSurjective τ₁₂] {f : M →ₛₗ[τ₁₂] M₂} (hf : Function.Surjective f)
    {p q : Submodule R M} (hpq : Codisjoint p q) : Codisjoint (p.map f) (q.map f) := by
  rw [codisjoint_iff, ← Submodule.map_sup, codisjoint_iff.mp hpq, Submodule.map_top,
    LinearMap.range_eq_top_of_surjective f hf]

