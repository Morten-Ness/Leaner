import Mathlib

open scoped Matrix

variable {R L M n ι ι' ιM : Type*}

variable [CommRing R] [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]

variable (φ : L →ₗ[R] Module.End R M)

variable [Fintype ι] [Fintype ι'] [Fintype ιM] [DecidableEq ι] [DecidableEq ι']

variable [DecidableEq ιM] (b : Basis ι R L) (bₘ : Basis ιM R M)

theorem polyCharpolyAux_map_eq_charpoly [Module.Finite R M] [Module.Free R M]
    (x : L) :
    (LinearMap.polyCharpolyAux φ b bₘ).map (MvPolynomial.eval (b.repr x)) = (φ x).charpoly := by
  nontriviality R
  rw [LinearMap.polyCharpolyAux_map_eq_toMatrix_charpoly, LinearMap.charpoly_toMatrix]

