import Mathlib

variable {ι ι' κ κ' : Type*}

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

variable {R₂ M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

variable (e : Basis ι R M) (v : ι' → M) (i : ι) (j : ι')

theorem toMatrix_smul_left {G} [Group G] [DistribMulAction G M] [SMulCommClass G R M] (g : G) :
    (g • e).toMatrix v = e.toMatrix (g⁻¹ • v) := rfl

