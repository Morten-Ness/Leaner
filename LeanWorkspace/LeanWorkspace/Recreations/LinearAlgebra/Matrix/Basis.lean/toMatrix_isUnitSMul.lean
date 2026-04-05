import Mathlib

variable {ι ι' κ κ' : Type*}

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

variable {R₂ M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

variable (e : Basis ι R M) (v : ι' → M) (i : ι) (j : ι')

theorem toMatrix_isUnitSMul [DecidableEq ι] (e : Module.Basis ι R₂ M₂) {w : ι → R₂}
    (hw : ∀ i, IsUnit (w i)) : e.toMatrix (e.isUnitSMul hw) = diagonal w := Module.Basis.toMatrix_unitsSMul e _

