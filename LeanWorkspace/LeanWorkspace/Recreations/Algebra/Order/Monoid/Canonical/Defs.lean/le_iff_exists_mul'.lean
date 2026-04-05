import Mathlib

variable {α : Type u}

variable [CommMagma α] [Preorder α] [CanonicallyOrderedMul α] {a b c : α}

theorem le_iff_exists_mul' : a ≤ b ↔ ∃ c, b = c * a := by
  simp only [mul_comm _ a, le_iff_exists_mul]

