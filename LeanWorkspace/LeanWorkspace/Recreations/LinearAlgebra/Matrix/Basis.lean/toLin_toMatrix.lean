import Mathlib

variable {ι ι' κ κ' : Type*}

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

variable {R₂ M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

variable (e : Basis ι R M) (v : ι' → M) (i : ι) (j : ι')

theorem toLin_toMatrix [Finite ι] [Fintype ι'] [DecidableEq ι'] (v : Module.Basis ι' R M) :
    Matrix.toLin v e (e.toMatrix v) = LinearMap.id := v.ext fun i => by cases nonempty_fintype ι; rw [toLin_self, id_apply, Module.Basis.sum_toMatrix_smul_self e]

