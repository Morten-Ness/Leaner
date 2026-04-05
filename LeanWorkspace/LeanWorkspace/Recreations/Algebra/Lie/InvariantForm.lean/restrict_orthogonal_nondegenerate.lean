import Mathlib

variable {K L M : Type*}

variable [Field K] [LieRing L] [LieAlgebra K L]

variable [AddCommGroup M] [Module K M] [LieRingModule L M]

variable [Module.Finite K L]

variable (Φ : LinearMap.BilinForm K L) (hΦ_nondeg : Φ.Nondegenerate)

variable (hΦ_inv : Φ.lieInvariant L) (hΦ_refl : Φ.IsRefl)

variable (hL : ∀ I : LieIdeal K L, IsAtom I → ¬IsLieAbelian I)

theorem restrict_orthogonal_nondegenerate (I : LieIdeal K L) (hI : IsAtom I) :
    (Φ.restrict (LieAlgebra.InvariantForm.orthogonal Φ hΦ_inv I)).Nondegenerate := by
  rw [LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal hΦ_refl]
  simp only [LieIdeal.toLieSubalgebra_toSubmodule, LieAlgebra.InvariantForm.orthogonal_toSubmodule,
    LinearMap.BilinForm.orthogonal_orthogonal hΦ_nondeg hΦ_refl]
  exact (LieAlgebra.InvariantForm.orthogonal_isCompl_toSubmodule Φ hΦ_nondeg hΦ_inv hΦ_refl hL I hI).symm

