import Mathlib

variable {R : Type u} [CommRing R]

variable {M N P Q : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    [Module R M] [Module R N] [Module R P] [Module R Q] [Coalgebra R M] [Coalgebra R N]
    [Coalgebra R P] [Coalgebra R Q]

set_option backward.isDefEq.respectTransparency false in
theorem tensorObj_comul (K L : CoalgCat R) :
    Coalgebra.comul (R := R) (A := (K ⊗ L : CoalgCat R))
      = (TensorProduct.tensorTensorTensorComm R K K L L).toLinearMap
      ∘ₗ TensorProduct.map Coalgebra.comul Coalgebra.comul := by
  rw [ofComonObjCoalgebraStruct_comul]
  simp only [Comon.monoidal_tensorObj_comon_comul, Equivalence.symm_inverse,
    comonEquivalence_functor, toComon_obj, toComonObj_X, ModuleCat.of_coe,
    MonObj.tensorObj.mul_def, unop_comp, unop_tensorObj, unop_tensorHom,
    BraidedCategory.unop_tensorμ, tensorμ_eq_tensorTensorTensorComm, ModuleCat.hom_comp,
    ModuleCat.hom_ofHom, LinearEquiv.comp_toLinearMap_eq_iff]
  rfl

