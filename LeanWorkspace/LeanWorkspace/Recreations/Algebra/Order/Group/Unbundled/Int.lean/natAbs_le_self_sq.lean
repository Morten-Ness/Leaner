import Mathlib

theorem natAbs_le_self_sq (a : ℤ) : (Int.natAbs a : ℤ) ≤ a ^ 2 := by
  rw [← Int.natAbs_sq a, sq]
  norm_cast
  apply Nat.le_mul_self

alias natAbs_le_self_pow_two := natAbs_le_self_sq

