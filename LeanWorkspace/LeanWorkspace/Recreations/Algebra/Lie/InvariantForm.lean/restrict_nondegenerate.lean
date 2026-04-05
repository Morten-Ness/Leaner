import Mathlib

variable {K L M : Type*}

variable [Field K] [LieRing L] [LieAlgebra K L]

variable [AddCommGroup M] [Module K M] [LieRingModule L M]

variable [Module.Finite K L]

variable (Φ : LinearMap.BilinForm K L) (hΦ_nondeg : Φ.Nondegenerate)

variable (hΦ_inv : Φ.lieInvariant L) (hΦ_refl : Φ.IsRefl)

variable (hL : ∀ I : LieIdeal K L, IsAtom I → ¬IsLieAbelian I)

theorem restrict_nondegenerate (I : LieIdeal K L) (hI : IsAtom I) :
    (Φ.restrict I).Nondegenerate := by
  rw [LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal hΦ_refl]
  exact LieAlgebra.InvariantForm.orthogonal_isCompl_toSubmodule Φ hΦ_nondeg hΦ_inv hΦ_refl hL I hI

