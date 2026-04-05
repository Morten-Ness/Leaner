import Mathlib

variable {M : Type*} [Monoid M] [LE M]

variable [MulLeftMono M] (u : Mˣ) {a b : M}

private theorem mul_le_mul_iff_left : u * a ≤ u * b ↔ a ≤ b := Units.mulLECancellable_val u.mul_le_mul_iff_left


theorem inv_mul_le_one : u⁻¹ * a ≤ 1 ↔ a ≤ u := by
  rw [Units.inv_mul_le_iff u, mul_one]

alias ⟨le_mul_of_inv_mul_le, inv_mul_le_of_le_mul⟩ := Units.inv_mul_le_iff
alias ⟨mul_le_of_le_inv_mul, le_inv_mul_of_mul_le⟩ := Units.le_inv_mul_iff
alias ⟨le_of_one_le_inv, one_le_inv_of_le⟩ := one_le_inv
alias ⟨le_of_inv_le_one, inv_le_one_of_le⟩ := inv_le_one
alias ⟨le_of_one_le_inv_mul, one_le_inv_mul_of_le⟩ := Units.one_le_inv_mul
alias ⟨le_of_inv_mul_le_one, inv_mul_le_one_of_le⟩ := inv_mul_le_one

