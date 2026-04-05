import Mathlib

section

variable {n : ℕ}

theorem sub_le_iff {n : ℕ} {a b : Fin n} : a - b ≤ a ↔ b ≤ a := by
  rw [← not_iff_not, Fin.not_le, Fin.not_le, Fin.lt_sub_iff]

end
