import Mathlib

variable (R : Type*) [CommRing R]

variable (L : Type*) [LieRing L] [LieAlgebra R L]

variable (M : Type*) [AddCommGroup M] [Module R M]

variable [LieRingModule L M] [LieModule R L M]

theorem d₁₂_apply_apply_ofTrivial [LieModule.IsTrivial L M] (f : oneCochain R L M) (x y : L) :
    LieModule.Cohomology.d₁₂ R L M f x y = - f ⁅x, y⁆ := by
  simp

