import Mathlib

variable {R L M : Type*}

variable [CommRing R] [LieRing L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable (Φ : LinearMap.BilinForm R M) (hΦ_nondeg : Φ.Nondegenerate)

variable (hΦ_inv : Φ.lieInvariant L)

theorem mem_orthogonal (N : LieSubmodule R L M) (y : M) :
    y ∈ LieAlgebra.InvariantForm.orthogonal Φ hΦ_inv N ↔ ∀ x ∈ N, Φ x y = 0 := by
  simp [LieAlgebra.InvariantForm.orthogonal, LinearMap.BilinForm.isOrtho_def, LinearMap.BilinForm.mem_orthogonal_iff]

