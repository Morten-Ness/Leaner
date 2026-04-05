import Mathlib

open scoped Matrix

variable {R L M n ι ι' ιM : Type*}

variable [CommRing R] [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]

variable (φ : L →ₗ[R] Module.End R M)

variable [Fintype ι] [Fintype ι'] [Fintype ιM] [DecidableEq ι] [DecidableEq ι']

variable [DecidableEq ιM] (b : Basis ι R L) (bₘ : Basis ιM R M)

theorem polyCharpolyAux_eval_eq_toMatrix_charpoly_coeff (x : L) (i : ℕ) :
    MvPolynomial.eval (b.repr x) ((LinearMap.polyCharpolyAux φ b bₘ).coeff i) =
      (toMatrix bₘ bₘ (φ x)).charpoly.coeff i := by
  simp [← LinearMap.polyCharpolyAux_map_eq_toMatrix_charpoly φ b bₘ x]

