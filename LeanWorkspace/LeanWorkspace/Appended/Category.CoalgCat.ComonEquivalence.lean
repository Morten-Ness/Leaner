import Mathlib

section

variable {R : Type u} [CommRing R]

variable {M N P Q : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    [Module R M] [Module R N] [Module R P] [Module R Q] [Coalgebra R M] [Coalgebra R N]
    [Coalgebra R P] [Coalgebra R Q]

theorem associator_hom_toLinearMap :
    (α_ (CoalgCat.of R M) (CoalgCat.of R N) (CoalgCat.of R P)).hom.1.toLinearMap
      = (TensorProduct.assoc R M N P).toLinearMap := TensorProduct.ext <| TensorProduct.ext <| by ext; rfl

end

section

variable {R : Type u} [CommRing R]

variable {M N P Q : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    [Module R M] [Module R N] [Module R P] [Module R Q] [Coalgebra R M] [Coalgebra R N]
    [Coalgebra R P] [Coalgebra R Q]

set_option backward.isDefEq.respectTransparency false in
theorem comul_tensorObj :
    Coalgebra.comul (R := R) (A := (CoalgCat.of R M ⊗ CoalgCat.of R N : CoalgCat R))
      = Coalgebra.comul (A := M ⊗[R] N) := by
  rw [ofComonObjCoalgebraStruct_comul]
  simp [tensorμ_eq_tensorTensorTensorComm, TensorProduct.comul_def,
    AlgebraTensorModule.tensorTensorTensorComm_eq]
  rfl

end

section

variable {R : Type u} [CommRing R]

variable {M N P Q : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    [Module R M] [Module R N] [Module R P] [Module R Q] [Coalgebra R M] [Coalgebra R N]
    [Coalgebra R P] [Coalgebra R Q]

set_option backward.isDefEq.respectTransparency false in
theorem comul_tensorObj_tensorObj_left :
    Coalgebra.comul (R := R)
      (A := ((CoalgCat.of R M ⊗ CoalgCat.of R N) ⊗ CoalgCat.of R P : CoalgCat R))
      = Coalgebra.comul (A := M ⊗[R] N ⊗[R] P) := by
  rw [ofComonObjCoalgebraStruct_comul]
  dsimp +instances
  simp +instances only [CoalgCat.toComonObj]
  simp [tensorμ_eq_tensorTensorTensorComm, TensorProduct.comul_def,
    AlgebraTensorModule.tensorTensorTensorComm_eq]
  rfl

end

section

variable {R : Type u} [CommRing R]

variable {M N P Q : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    [Module R M] [Module R N] [Module R P] [Module R Q] [Coalgebra R M] [Coalgebra R N]
    [Coalgebra R P] [Coalgebra R Q]

set_option backward.isDefEq.respectTransparency false in
theorem comul_tensorObj_tensorObj_right :
    Coalgebra.comul (R := R) (A := (CoalgCat.of R M ⊗
      (CoalgCat.of R N ⊗ CoalgCat.of R P) : CoalgCat R))
      = Coalgebra.comul (A := M ⊗[R] (N ⊗[R] P)) := by
  rw [ofComonObjCoalgebraStruct_comul]
  simp only [Comon.monoidal_tensorObj_comon_comul]
  simp [tensorμ_eq_tensorTensorTensorComm, TensorProduct.comul_def,
    AlgebraTensorModule.tensorTensorTensorComm_eq]
  rfl

end

section

variable {R : Type u} [CommRing R]

variable {M N P Q : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    [Module R M] [Module R N] [Module R P] [Module R Q] [Coalgebra R M] [Coalgebra R N]
    [Coalgebra R P] [Coalgebra R Q]

set_option backward.isDefEq.respectTransparency false in
theorem counit_tensorObj :
    Coalgebra.counit (R := R) (A := (CoalgCat.of R M ⊗ CoalgCat.of R N : CoalgCat R))
      = Coalgebra.counit (A := M ⊗[R] N) := by
  rw [ofComonObjCoalgebraStruct_counit]
  simp [TensorProduct.counit_def, TensorProduct.AlgebraTensorModule.rid_eq_rid, ← lid_eq_rid]
  rfl

end

section

variable {R : Type u} [CommRing R]

variable {M N P Q : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    [Module R M] [Module R N] [Module R P] [Module R Q] [Coalgebra R M] [Coalgebra R N]
    [Coalgebra R P] [Coalgebra R Q]

set_option backward.isDefEq.respectTransparency false in
theorem counit_tensorObj_tensorObj_left :
    Coalgebra.counit (R := R)
      (A := ((CoalgCat.of R M ⊗ CoalgCat.of R N) ⊗ CoalgCat.of R P : CoalgCat R))
      = Coalgebra.counit (A := (M ⊗[R] N) ⊗[R] P) := by
  rw [ofComonObjCoalgebraStruct_counit]
  simp [TensorProduct.counit_def, TensorProduct.AlgebraTensorModule.rid_eq_rid, ← lid_eq_rid]
  rfl

end

section

variable {R : Type u} [CommRing R]

variable {M N P Q : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    [Module R M] [Module R N] [Module R P] [Module R Q] [Coalgebra R M] [Coalgebra R N]
    [Coalgebra R P] [Coalgebra R Q]

set_option backward.isDefEq.respectTransparency false in
theorem counit_tensorObj_tensorObj_right :
    Coalgebra.counit (R := R)
      (A := (CoalgCat.of R M ⊗ (CoalgCat.of R N ⊗ CoalgCat.of R P) : CoalgCat R))
      = Coalgebra.counit (A := M ⊗[R] (N ⊗[R] P)) := by
  rw [ofComonObjCoalgebraStruct_counit]
  simp [TensorProduct.counit_def, TensorProduct.AlgebraTensorModule.rid_eq_rid, ← lid_eq_rid]
  rfl

end

section

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

end
