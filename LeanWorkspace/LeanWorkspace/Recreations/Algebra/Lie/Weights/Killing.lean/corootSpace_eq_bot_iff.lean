import Mathlib

variable (R K L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [Field K] [LieAlgebra K L]

variable [FiniteDimensional K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

variable [IsKilling K L]

variable [IsTriangularizable K H L]

variable [CharZero K]

theorem corootSpace_eq_bot_iff {α : Weight K H L} :
    corootSpace α = ⊥ ↔ α.IsZero := by
  simp [← LieSubmodule.toSubmodule_eq_bot, LieAlgebra.IsKilling.coe_corootSpace_eq_span_singleton α]

