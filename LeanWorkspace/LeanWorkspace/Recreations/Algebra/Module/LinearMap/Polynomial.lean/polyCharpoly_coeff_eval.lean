import Mathlib

open scoped Matrix

variable {R L M n ι ι' ιM : Type*}

variable [CommRing R] [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]

variable (φ : L →ₗ[R] Module.End R M)

variable [Fintype ι] [Fintype ι'] [Fintype ιM] [DecidableEq ι] [DecidableEq ι']

variable [Module.Free R M] [Module.Finite R M] (b : Basis ι R L)

theorem polyCharpoly_coeff_eval (x : L) (i : ℕ) :
    MvPolynomial.eval (b.repr x) ((LinearMap.polyCharpoly φ b).coeff i) = (φ x).charpoly.coeff i := by
  rw [LinearMap.polyCharpoly, LinearMap.polyCharpolyAux_coeff_eval]

