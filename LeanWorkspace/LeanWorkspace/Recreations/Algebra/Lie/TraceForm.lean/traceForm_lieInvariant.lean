import Mathlib

variable (R K L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

theorem traceForm_lieInvariant : (LieModule.traceForm R L M).lieInvariant L := by
  intro x y z
  rw [← lie_skew, map_neg, LinearMap.neg_apply, LieModule.traceForm_apply_lie_apply R L M]

