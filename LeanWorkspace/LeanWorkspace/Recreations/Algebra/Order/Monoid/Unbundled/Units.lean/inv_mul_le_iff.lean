import Mathlib

variable {M : Type*} [Monoid M] [LE M]

variable [MulLeftMono M] (u : Mˣ) {a b : M}

private theorem mul_le_mul_iff_left : u * a ≤ u * b ↔ a ≤ b := Units.mulLECancellable_val u.mul_le_mul_iff_left


theorem inv_mul_le_iff : u⁻¹ * a ≤ b ↔ a ≤ u * b := by
  rw [← mul_le_mul_iff_left u, mul_inv_cancel_left]

