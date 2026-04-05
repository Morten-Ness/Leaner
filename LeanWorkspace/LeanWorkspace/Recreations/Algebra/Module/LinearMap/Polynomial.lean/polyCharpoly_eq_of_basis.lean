import Mathlib

open scoped Matrix

variable {R L M n ι ι' ιM : Type*}

variable [CommRing R] [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]

variable (φ : L →ₗ[R] Module.End R M)

variable [Fintype ι] [Fintype ι'] [Fintype ιM] [DecidableEq ι] [DecidableEq ι']

variable [Module.Free R M] [Module.Finite R M] (b : Basis ι R L)

theorem polyCharpoly_eq_of_basis [DecidableEq ιM] (bₘ : Module.Basis ιM R M) :
    LinearMap.polyCharpoly φ b =
    (Matrix.charpoly.univ R ιM).map (MvPolynomial.bind₁ (φ.toMvPolynomial b bₘ.end)) := by
  rw [LinearMap.polyCharpoly, φ.polyCharpolyAux_basisIndep b (Module.Free.chooseBasis R M) bₘ,
    LinearMap.polyCharpolyAux]

