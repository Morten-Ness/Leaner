import Mathlib

variable (R K L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

theorem traceForm_apply_lie_apply' (x y z : L) :
    LieModule.traceForm R L M ⁅x, y⁆ z = - LieModule.traceForm R L M y ⁅x, z⁆ := calc LieModule.traceForm R L M ⁅x, y⁆ z
      = - LieModule.traceForm R L M ⁅y, x⁆ z := by rw [← lie_skew x y, map_neg, LinearMap.neg_apply]
    _ = - LieModule.traceForm R L M y ⁅x, z⁆ := by rw [LieModule.traceForm_apply_lie_apply]

