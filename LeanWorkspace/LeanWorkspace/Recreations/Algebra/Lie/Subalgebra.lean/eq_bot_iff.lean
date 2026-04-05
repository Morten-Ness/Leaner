import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

variable {L₂ : Type w} [LieRing L₂] [LieAlgebra R L₂]

variable (f : L →ₗ⁅R⁆ L₂)

variable (K K' : LieSubalgebra R L) (K₂ : LieSubalgebra R L₂)

theorem eq_bot_iff : K = ⊥ ↔ ∀ x : L, x ∈ K → x = 0 := by
  rw [_root_.eq_bot_iff]
  exact Iff.rfl

