import Mathlib

variable {M : Type*} [Monoid M] [LE M]

variable [MulLeftMono M] (u : Mˣ) {a b : M}

theorem mulLECancellable_val : MulLECancellable (↑u : M) := fun _ _ h ↦ by
  simpa using mul_le_mul_right h ↑u⁻¹

