import Mathlib

theorem Int.associated_iff {a b : ℤ} : Associated a b ↔ a = b ∨ a = -b := by
  rw [Int.associated_iff_natAbs]
  exact Int.natAbs_eq_natAbs_iff

