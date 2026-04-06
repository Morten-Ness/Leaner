import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem mem_map_equiv {f : M ≃* N} {K : Subsemigroup M} {x : N} :
    x ∈ K.map (f : M →ₙ* N) ↔ f.symm x ∈ K := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    refine ⟨f.symm x, hx, ?_⟩
    exact f.apply_symm_apply x
