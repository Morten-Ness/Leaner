import Mathlib

variable (R : Type*) [CommRing R]

variable (L : Type*) [LieRing L] [LieAlgebra R L]

variable (M : Type*) [AddCommGroup M] [Module R M]

variable [LieRingModule L M] [LieModule R L M]

set_option backward.privateInPublic true in
private def d₂₃_aux (a : LieModule.Cohomology.twoCochain R L M) : L →ₗ[R] L →ₗ[R] L →ₗ[R] M where
  toFun x := { toFun y :=
        { toFun z := ⁅x, a y z⁆ - ⁅y, a x z⁆ + ⁅z, a x y⁆ - a ⁅x, y⁆ z + a ⁅x, z⁆ y - a ⁅y, z⁆ x
          map_add' _ _ := by simp; abel
          map_smul' _ _ := by abel_nf; simp }
      map_add' _ _ := by ext; simp; abel
      map_smul' _ _ := by ext; abel_nf; simp }
  map_add' _ _ := by ext; simp; abel
  map_smul' _ _ := by ext; abel_nf; simp


theorem d₂₃_apply (a : LieModule.Cohomology.twoCochain R L M) (x y z : L) :
    LieModule.Cohomology.d₂₃ R L M a x y z =
      ⁅x, a y z⁆ - ⁅y, a x z⁆ + ⁅z, a x y⁆ - a ⁅x, y⁆ z + a ⁅x, z⁆ y - a ⁅y, z⁆ x := rfl

