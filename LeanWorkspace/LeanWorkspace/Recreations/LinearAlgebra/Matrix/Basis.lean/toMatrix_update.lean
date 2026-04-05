import Mathlib

variable {ι ι' κ κ' : Type*}

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

variable {R₂ M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

variable (e : Basis ι R M) (v : ι' → M) (i : ι) (j : ι')

theorem toMatrix_update [DecidableEq ι'] (x : M) :
    e.toMatrix (Function.update v j x) = Matrix.updateCol (e.toMatrix v) j (e.repr x) := by
  ext i' k
  rw [Module.Basis.toMatrix, Matrix.updateCol_apply, Module.Basis.toMatrix_apply e]
  split_ifs with h
  · rw [h, update_self j x v]
  · rw [update_of_ne h]

