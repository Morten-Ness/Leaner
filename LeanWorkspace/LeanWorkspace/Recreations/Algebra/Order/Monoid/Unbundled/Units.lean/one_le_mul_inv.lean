import Mathlib

variable {M : Type*} [Monoid M] [LE M]

variable [MulRightMono M] {a b : M} (u : Mˣ)

private theorem mul_le_mul_iff_left : u * a ≤ u * b ↔ a ≤ b := Units.mulLECancellable_val u.mul_le_mul_iff_left


private theorem mul_le_mul_iff_right : a * u ≤ b * u ↔ a ≤ b := ⟨(by simpa using mul_le_mul_left · ↑u⁻¹), (mul_le_mul_left · _)⟩


theorem one_le_mul_inv : 1 ≤ a * u⁻¹ ↔ u ≤ a := by
  rw [Units.le_mul_inv_iff u, one_mul]

