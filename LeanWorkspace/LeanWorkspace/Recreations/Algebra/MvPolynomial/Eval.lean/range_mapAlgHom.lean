import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable (f : R →+* S₁)

theorem range_mapAlgHom [CommSemiring S₂] [Algebra R S₁] [Algebra R S₂] (f : S₁ →ₐ[R] S₂) :
    (MvPolynomial.mapAlgHom f).range.toSubmodule = coeffsIn σ f.range.toSubmodule := by
  ext
  rw [Subalgebra.mem_toSubmodule, ← SetLike.mem_coe, AlgHom.coe_range, MvPolynomial.mapAlgHom, AlgHom.coe_mk,
    MvPolynomial.mem_range_map_iff_coeffs_subset, mem_coeffsIn_iff_coeffs_subset]
  simp [Set.subset_def]

