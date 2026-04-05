import Mathlib

variable {M : Type*} [Monoid M] [LE M]

variable [MulRightMono M] {a b : M} (u : Mˣ)

private theorem mul_le_mul_iff_left : u * a ≤ u * b ↔ a ≤ b := Units.mulLECancellable_val u.mul_le_mul_iff_left


private theorem mul_le_mul_iff_right : a * u ≤ b * u ↔ a ≤ b := ⟨(by simpa using mul_le_mul_left · ↑u⁻¹), (mul_le_mul_left · _)⟩


theorem mul_inv_le_one : a * u⁻¹ ≤ 1 ↔ a ≤ u := by
  rw [Units.mul_inv_le_iff u, one_mul]

alias ⟨le_mul_of_mul_inv_le, mul_inv_le_of_le_mul⟩ := Units.mul_inv_le_iff
alias ⟨mul_le_of_le_mul_inv, le_mul_inv_of_mul_le⟩ := Units.le_mul_inv_iff
alias ⟨le_of_one_le_mul_inv, one_le_mul_inv_of_le⟩ := Units.one_le_mul_inv
alias ⟨le_of_mul_inv_le_one, mul_inv_le_one_of_le⟩ := mul_inv_le_one

