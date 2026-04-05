import Mathlib

variable {M : Type*} [Monoid M] [LE M]

variable [MulRightMono M] {a b : M} (u : Mˣ)

private theorem mul_le_mul_iff_left : u * a ≤ u * b ↔ a ≤ b := Units.mulLECancellable_val u.mul_le_mul_iff_left


private theorem mul_le_mul_iff_right : a * u ≤ b * u ↔ a ≤ b := ⟨(by simpa using mul_le_mul_left · ↑u⁻¹), (mul_le_mul_left · _)⟩


theorem le_mul_inv_iff : a ≤ b * u⁻¹ ↔ a * u ≤ b := by
  rw [← mul_le_mul_iff_right u, inv_mul_cancel_right]

