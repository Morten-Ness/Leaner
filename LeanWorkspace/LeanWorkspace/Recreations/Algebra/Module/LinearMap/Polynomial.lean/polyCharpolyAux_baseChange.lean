import Mathlib

open scoped Matrix

variable {R L M n ι ι' ιM : Type*}

variable [CommRing R] [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]

variable (φ : L →ₗ[R] Module.End R M)

variable [Fintype ι] [Fintype ι'] [Fintype ιM] [DecidableEq ι] [DecidableEq ι']

variable [DecidableEq ιM] (b : Basis ι R L) (bₘ : Basis ιM R M)

theorem polyCharpolyAux_baseChange (A : Type*) [CommRing A] [Algebra R A] :
    LinearMap.polyCharpolyAux (tensorProduct _ _ _ _ ∘ₗ φ.baseChange A) (basis A b) (basis A bₘ) =
      (LinearMap.polyCharpolyAux φ b bₘ).map (MvPolynomial.map (algebraMap R A)) := by
  simp only [LinearMap.polyCharpolyAux]
  rw [← Matrix.charpoly.univ_map_map _ (algebraMap R A)]
  simp only [Polynomial.map_map]
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, map_C, bind₁_C_right]
  · rintro ij
    simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, map_X, bind₁_X_right]
    classical
    rw [LinearMap.toMvPolynomial_comp _ (basis A (Module.Basis.end bₘ)), ← LinearMap.toMvPolynomial_baseChange]
    suffices LinearMap.toMvPolynomial (M₂ := (Module.End A (TensorProduct R A M)))
        (basis A bₘ.end) (basis A bₘ).end (tensorProduct R A M M) ij = X ij by
      rw [this, bind₁_X_right]
    simp only [LinearMap.toMvPolynomial, Matrix.toMvPolynomial]
    suffices ∀ kl,
        (toMatrix (basis A bₘ.end) (basis A bₘ).end) (tensorProduct R A M M) ij kl =
        if kl = ij then 1 else 0 by
      rw [Finset.sum_eq_single ij]
      · rw [this, if_pos rfl, X]
      · rintro kl - H
        rw [this, if_neg H, map_zero]
      · grind
    intro kl
    rw [toMatrix_apply, tensorProduct, TensorProduct.AlgebraTensorModule.lift_apply,
      basis_apply, TensorProduct.lift.tmul, coe_restrictScalars]
    dsimp only [coe_mk, AddHom.coe_mk, smul_apply, baseChangeHom_apply]
    rw [one_smul, Module.Basis.baseChange_end, Module.Basis.repr_self_apply]

