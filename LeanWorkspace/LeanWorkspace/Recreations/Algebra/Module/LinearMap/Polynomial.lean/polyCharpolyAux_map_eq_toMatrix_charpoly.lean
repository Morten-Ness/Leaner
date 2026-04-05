import Mathlib

open scoped Matrix

variable {R L M n ι ι' ιM : Type*}

variable [CommRing R] [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]

variable (φ : L →ₗ[R] Module.End R M)

variable [Fintype ι] [Fintype ι'] [Fintype ιM] [DecidableEq ι] [DecidableEq ι']

variable [DecidableEq ιM] (b : Basis ι R L) (bₘ : Basis ιM R M)

theorem polyCharpolyAux_map_eq_toMatrix_charpoly (x : L) :
    (LinearMap.polyCharpolyAux φ b bₘ).map (MvPolynomial.eval (b.repr x)) =
      (toMatrix bₘ bₘ (φ x)).charpoly := by
  rw [LinearMap.polyCharpolyAux, Polynomial.map_map, ← MvPolynomial.eval₂Hom_C_eq_bind₁,
    MvPolynomial.comp_eval₂Hom, Matrix.charpoly.univ_map_eval₂Hom]
  congr
  ext
  rw [of_apply, Function.curry_apply, LinearMap.toMvPolynomial_eval_eq_apply, LinearEquiv.symm_apply_apply]
  rfl

