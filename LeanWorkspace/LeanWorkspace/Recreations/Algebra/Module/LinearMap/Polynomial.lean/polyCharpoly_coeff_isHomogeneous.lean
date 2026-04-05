import Mathlib

open scoped Matrix

variable {R L M n ι ι' ιM : Type*}

variable [CommRing R] [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]

variable (φ : L →ₗ[R] Module.End R M)

variable [Fintype ι] [Fintype ι'] [Fintype ιM] [DecidableEq ι] [DecidableEq ι']

variable [Module.Free R M] [Module.Finite R M] (b : Basis ι R L)

theorem polyCharpoly_coeff_isHomogeneous (i j : ℕ) (hij : i + j = finrank R M) [Nontrivial R] :
    ((LinearMap.polyCharpoly φ b).coeff i).IsHomogeneous j := by
  rw [finrank_eq_card_chooseBasisIndex] at hij
  rw [LinearMap.polyCharpoly, LinearMap.polyCharpolyAux, Polynomial.coeff_map, ← one_mul j]
  apply (Matrix.charpoly.univ_coeff_isHomogeneous _ _ _ _ hij).eval₂
  · exact fun r ↦ MvPolynomial.isHomogeneous_C _ _
  · exact LinearMap.toMvPolynomial_isHomogeneous _ _ _

