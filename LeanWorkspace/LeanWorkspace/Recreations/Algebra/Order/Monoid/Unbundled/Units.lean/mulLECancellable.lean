import Mathlib

variable {M : Type*} [Monoid M] [LE M]

variable [MulLeftMono M] {a b c : M} (ha : IsUnit a)

private theorem mul_le_mul_iff_left : u * a ≤ u * b ↔ a ≤ b := Units.mulLECancellable_val u.mul_le_mul_iff_left


private theorem mul_le_mul_iff_right : a * u ≤ b * u ↔ a ≤ b := ⟨(by simpa using mul_le_mul_left · ↑u⁻¹), (mul_le_mul_left · _)⟩


theorem mulLECancellable : MulLECancellable a := Units.mulLECancellable_val ha.unit

