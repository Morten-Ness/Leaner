import Mathlib

variable {M : Type*} [Monoid M] [LE M]

variable [MulRightMono M] {a b c : M} (hc : IsUnit c)

private theorem mul_le_mul_iff_left : u * a ≤ u * b ↔ a ≤ b := Units.mulLECancellable_val u.mul_le_mul_iff_left


private theorem mul_le_mul_iff_right : a * u ≤ b * u ↔ a ≤ b := ⟨(by simpa using mul_le_mul_left · ↑u⁻¹), (mul_le_mul_left · _)⟩


theorem mul_le_mul_right : a * c ≤ b * c ↔ a ≤ b := mul_le_mul_iff_right hc.unit

alias ⟨le_of_mul_le_mul_right, _⟩ := mul_le_mul_right

