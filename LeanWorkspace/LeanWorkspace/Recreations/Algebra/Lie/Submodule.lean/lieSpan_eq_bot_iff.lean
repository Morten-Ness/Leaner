import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

variable (R L) (s : Set M)

theorem lieSpan_eq_bot_iff : LieSubmodule.lieSpan R L s = ⊥ ↔ ∀ m ∈ s, m = (0 : M) := by
  rw [_root_.eq_bot_iff, LieSubmodule.lieSpan_le, LieSubmodule.bot_coe, subset_singleton_iff]

