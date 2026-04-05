import Mathlib

open scoped Matrix

variable {R L M n ι ι' ιM : Type*}

variable [CommRing R] [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]

variable (φ : L →ₗ[R] Module.End R M)

variable [Fintype ι] [Fintype ι'] [Fintype ιM] [DecidableEq ι] [DecidableEq ι']

variable [Module.Free R M] [Module.Finite R M] (b : Basis ι R L)

theorem polyCharpoly_natDegree [Nontrivial R] :
    (LinearMap.polyCharpoly φ b).natDegree = finrank R M := by
  rw [LinearMap.polyCharpoly, LinearMap.polyCharpolyAux, (Matrix.charpoly.univ_monic _ _).natDegree_map,
    Matrix.charpoly.univ_natDegree, finrank_eq_card_chooseBasisIndex]

