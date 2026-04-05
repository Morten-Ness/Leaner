import Mathlib

variable (R K L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

theorem traceForm_apply_lie_apply (x y z : L) :
    LieModule.traceForm R L M ⁅x, y⁆ z = LieModule.traceForm R L M x ⁅y, z⁆ := by
  calc LieModule.traceForm R L M ⁅x, y⁆ z
      = trace R _ (φ ⁅x, y⁆ ∘ₗ φ z) := by simp only [LieModule.traceForm_apply_apply]
    _ = trace R _ ((φ x * φ y - φ y * φ x) * φ z) := ?_
    _ = trace R _ (φ x * (φ y * φ z)) - trace R _ (φ y * (φ x * φ z)) := ?_
    _ = trace R _ (φ x * (φ y * φ z)) - trace R _ (φ x * (φ z * φ y)) := ?_
    _ = LieModule.traceForm R L M x ⁅y, z⁆ := ?_
  · simp only [LieHom.map_lie, Ring.lie_def, ← Module.End.mul_eq_comp]
  · simp only [sub_mul, map_sub, mul_assoc]
  · simp only [LinearMap.trace_mul_cycle' R (φ x) (φ z) (φ y)]
  · simp only [LieModule.traceForm_apply_apply, LieHom.map_lie, Ring.lie_def, mul_sub, map_sub,
      ← Module.End.mul_eq_comp]

