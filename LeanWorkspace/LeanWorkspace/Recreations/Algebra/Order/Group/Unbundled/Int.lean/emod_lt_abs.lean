import Mathlib

theorem emod_lt_abs (a : ℤ) {b : ℤ} (H : b ≠ 0) : a % b < |b| := by
  rw [← Int.emod_abs]; exact emod_lt_of_pos _ (abs_pos.2 H)

