import Mathlib

variable (R : Type u) (L : Type v) (M : Type w)

variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M] [LieModule R L M]

theorem LieModule.toEnd_lie (x y : L) (z : M) :
    (φ x) ⁅y, z⁆ = ⁅ad R L x y, z⁆ + ⁅y, φ x z⁆ := by
  simp

