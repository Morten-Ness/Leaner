import Mathlib

variable {ι ι' κ κ' : Type*}

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

variable {R₂ M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

variable (e : Basis ι R M) (v : ι' → M) (i : ι) (j : ι')

theorem toMatrix_self [DecidableEq ι] : e.toMatrix e = 1 := by
  unfold Module.Basis.toMatrix
  ext i j
  simp [Matrix.one_apply, Finsupp.single_apply, eq_comm]

