import Mathlib

open scoped Matrix

variable {R L M n ι ι' ιM : Type*}

variable [CommRing R] [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]

variable (φ : L →ₗ[R] Module.End R M)

variable [Fintype ι] [Fintype ι'] [Fintype ιM] [DecidableEq ι] [DecidableEq ι']

variable [Module.Free R M] [Module.Finite R M] (b : Basis ι R L)

theorem polyCharpoly_baseChange (A : Type*) [CommRing A] [Algebra R A] :
    LinearMap.polyCharpoly (tensorProduct _ _ _ _ ∘ₗ φ.baseChange A) (basis A b) =
      (LinearMap.polyCharpoly φ b).map (MvPolynomial.map (algebraMap R A)) := by
  unfold LinearMap.polyCharpoly
  rw [← φ.polyCharpolyAux_baseChange]
  apply LinearMap.polyCharpolyAux_basisIndep

