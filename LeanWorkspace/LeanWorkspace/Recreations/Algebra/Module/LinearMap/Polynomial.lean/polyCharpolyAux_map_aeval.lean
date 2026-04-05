import Mathlib

open scoped Matrix

variable {R L M n ι ι' ιM : Type*}

variable [CommRing R] [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]

variable (φ : L →ₗ[R] Module.End R M)

variable [Fintype ι] [Fintype ι'] [Fintype ιM] [DecidableEq ι] [DecidableEq ι']

variable [DecidableEq ιM] (b : Basis ι R L) (bₘ : Basis ιM R M)

theorem polyCharpolyAux_map_aeval
    (A : Type*) [CommRing A] [Algebra R A] [Module.Finite A (A ⊗[R] M)] [Module.Free A (A ⊗[R] M)]
    (x : ι → A) :
    (LinearMap.polyCharpolyAux φ b bₘ).map (MvPolynomial.aeval x).toRingHom =
      LinearMap.charpoly ((tensorProduct R A M M).comp (baseChange A φ)
        ((basis A b).repr.symm (Finsupp.equivFunOnFinite.symm x))) := by
  rw [← LinearMap.polyCharpolyAux_map_eval (tensorProduct R A M M ∘ₗ baseChange A φ) _ (basis A bₘ),
    LinearMap.polyCharpolyAux_baseChange, Polynomial.map_map]
  congr
  exact DFunLike.ext _ _ fun f ↦ (MvPolynomial.eval_map (algebraMap R A) x f).symm

