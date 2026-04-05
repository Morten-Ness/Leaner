import Mathlib

open scoped Matrix

variable {R L M n ι ι' ιM : Type*}

variable [CommRing R] [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]

variable (φ : L →ₗ[R] Module.End R M)

variable [Fintype ι] [Fintype ι'] [Fintype ιM] [DecidableEq ι] [DecidableEq ι']

variable [DecidableEq ιM] (b : Basis ι R L) (bₘ : Basis ιM R M)

theorem polyCharpolyAux_coeff_eval [Module.Finite R M] [Module.Free R M] (x : L) (i : ℕ) :
    MvPolynomial.eval (b.repr x) ((LinearMap.polyCharpolyAux φ b bₘ).coeff i) = (φ x).charpoly.coeff i := by
  nontriviality R
  rw [← LinearMap.polyCharpolyAux_map_eq_charpoly φ b bₘ x, Polynomial.coeff_map]

