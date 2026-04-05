import Mathlib

variable {R L M : Type*}

variable [CommRing R] [LieRing L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable (Φ : LinearMap.BilinForm R M) (hΦ_nondeg : Φ.Nondegenerate)

variable (hΦ_inv : Φ.lieInvariant L)

theorem orthogonal_toSubmodule (N : LieSubmodule R L M) :
    (LieAlgebra.InvariantForm.orthogonal Φ hΦ_inv N).toSubmodule = Φ.orthogonal N.toSubmodule := rfl

