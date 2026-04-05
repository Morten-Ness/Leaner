import Mathlib

variable {M : Type*} [Monoid M] [LE M]

variable [MulLeftMono M] (u : Mˣ) {a b : M}

private theorem mul_le_mul_iff_left : u * a ≤ u * b ↔ a ≤ b := Units.mulLECancellable_val u.mul_le_mul_iff_left


theorem one_le_inv_mul : 1 ≤ u⁻¹ * a ↔ u ≤ a := by
  rw [Units.le_inv_mul_iff u, mul_one]

