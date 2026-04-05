import Mathlib

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

