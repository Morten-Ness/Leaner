import Mathlib

variable {M : Type*} [Monoid M] [LE M]

variable [MulLeftMono M] (u : Mˣ) {a b : M}

private theorem mul_le_mul_iff_left : u * a ≤ u * b ↔ a ≤ b := Units.mulLECancellable_val u.mul_le_mul_iff_left


theorem le_inv_mul_iff : a ≤ u⁻¹ * b ↔ u * a ≤ b := by
  rw [← mul_le_mul_iff_left u, mul_inv_cancel_left]

