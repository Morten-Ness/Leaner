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


theorem mem_twoCocycle_iff_of_trivial [LieModule.IsTrivial L M] (a : LieModule.Cohomology.twoCochain R L M) :
    a ∈ LieModule.Cohomology.twoCocycle R L M ↔
      ∀ (x y z : L), a x ⁅y, z⁆ = a ⁅x, y⁆ z + a y ⁅x, z⁆ := by
  constructor
  · intro h x y z
    rw [LieModule.Cohomology.mem_twoCocycle_iff] at h
    have : (LieModule.Cohomology.d₂₃ R L M) a x y z = 0 := (congrArg (fun b ↦ b x y z = 0) h).mpr rfl
    simp only [LieModule.Cohomology.d₂₃_apply, trivial_lie_zero, sub_self, add_zero, zero_sub] at this
    rw [sub_eq_zero] at this
    rw [← LieModule.Cohomology.twoCochain_skew a _ x, ← LieModule.Cohomology.twoCochain_skew a _ y, ← this]
    abel
  · intro h
    ext x y z
    simp only [LieModule.Cohomology.d₂₃_apply, trivial_lie_zero, sub_self, add_zero, zero_sub, LinearMap.zero_apply]
    rw [← LieModule.Cohomology.twoCochain_skew a x, ← LieModule.Cohomology.twoCochain_skew a y, h x y z]
    abel

