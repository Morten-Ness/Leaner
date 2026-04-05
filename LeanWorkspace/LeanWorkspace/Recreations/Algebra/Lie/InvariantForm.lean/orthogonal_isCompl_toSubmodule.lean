import Mathlib

variable {K L M : Type*}

variable [Field K] [LieRing L] [LieAlgebra K L]

variable [AddCommGroup M] [Module K M] [LieRingModule L M]

variable [Module.Finite K L]

variable (Φ : LinearMap.BilinForm K L) (hΦ_nondeg : Φ.Nondegenerate)

variable (hΦ_inv : Φ.lieInvariant L) (hΦ_refl : Φ.IsRefl)

variable (hL : ∀ I : LieIdeal K L, IsAtom I → ¬IsLieAbelian I)

theorem orthogonal_isCompl_toSubmodule (I : LieIdeal K L) (hI : IsAtom I) :
    IsCompl I.toSubmodule (LieAlgebra.InvariantForm.orthogonal Φ hΦ_inv I).toSubmodule := by
  rw [LieAlgebra.InvariantForm.orthogonal_toSubmodule, LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint hΦ_refl,
      ← LieAlgebra.InvariantForm.orthogonal_toSubmodule _ hΦ_inv, LieSubmodule.disjoint_toSubmodule]
  exact LieAlgebra.InvariantForm.orthogonal_disjoint Φ hΦ_nondeg hΦ_inv hL I hI

