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


theorem d₂₃_comp_d₁₂ : (LieModule.Cohomology.d₂₃ R L M) ∘ₗ (LieModule.Cohomology.d₁₂ R L M) = 0 := by
  ext a x y z
  have (a : oneCochain R L M) (x : L) : LieModule.Cohomology.d₁₂ R L M a x = (LieModule.Cohomology.d₁₂ R L M a).val x := rfl
  simp only [LinearMap.comp_apply, LieModule.Cohomology.d₂₃_apply, LinearMap.zero_apply, this,
    d₁₂_apply_coe_apply_apply R L M, lie_sub, lie_lie]
  rw [leibniz_lie y x, leibniz_lie z x, leibniz_lie z y]
  have : a ⁅y, ⁅z, x⁆⁆ = a ⁅x, ⁅z, y⁆⁆ + a ⁅z, ⁅y, x⁆⁆ := by
    rw [congr_arg a (leibniz_lie y z x), ← lie_skew, ← lie_skew z y, lie_neg, map_add]
  simp only [lie_lie, sub_add_cancel, map_sub, ← lie_skew x y, ← lie_skew x z, ← lie_skew y z,
    lie_neg, map_neg, this]
  abel

