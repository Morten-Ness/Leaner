import Mathlib

variable {α : Type u}

variable [Group α] [LinearOrder α]

variable [MulLeftMono α]

variable {a b : α}

theorem div_le_inv_mul_iff [MulRightMono α] :
    a / b ≤ a⁻¹ * b ↔ a ≤ b := by
  rw [div_eq_mul_inv, mul_inv_le_inv_mul_iff]
  exact
    ⟨fun h => not_lt.mp fun k => not_lt.mpr h (mul_lt_mul_of_lt_of_lt k k), fun h =>
      mul_le_mul' h h⟩

-- What is the point of this lemma?  See comment about `div_le_inv_mul_iff` above.
-- Note: we intentionally don't have `@[simp]` for the additive version,
-- since the LHS simplifies with `tsub_le_iff_right`

