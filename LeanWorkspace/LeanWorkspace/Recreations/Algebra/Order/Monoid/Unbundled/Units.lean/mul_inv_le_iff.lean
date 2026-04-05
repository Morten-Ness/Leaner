import Mathlib

variable {M : Type*} [Monoid M] [LE M]

variable [MulRightMono M] {a b : M} (u : Mˣ)

private theorem mul_le_mul_iff_left : u * a ≤ u * b ↔ a ≤ b := Units.mulLECancellable_val u.mul_le_mul_iff_left


private theorem mul_le_mul_iff_right : a * u ≤ b * u ↔ a ≤ b := ⟨(by simpa using mul_le_mul_left · ↑u⁻¹), (mul_le_mul_left · _)⟩


theorem mul_inv_le_iff : a * u⁻¹ ≤ b ↔ a ≤ b * u := by
  rw [← mul_le_mul_iff_right u, u.inv_mul_cancel_right]

