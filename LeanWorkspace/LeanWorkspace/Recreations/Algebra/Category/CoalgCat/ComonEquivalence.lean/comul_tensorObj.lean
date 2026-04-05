import Mathlib

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

