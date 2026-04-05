import Mathlib

variable {α : Type u}

variable [Group α] [LE α]

variable [MulRightMono α] {a b c : α}

theorem div_le_iff_le_mul : a / c ≤ b ↔ a ≤ b * c := by
  rw [← mul_le_mul_iff_right c, div_eq_mul_inv, inv_mul_cancel_right]

-- Note: we intentionally don't have `@[simp]` for the additive version,
-- since the LHS simplifies with `tsub_le_iff_right`
attribute [simp] div_le_iff_le_mul

-- TODO: Should we get rid of `sub_le_iff_le_add` in favor of
-- (a renamed version of) `tsub_le_iff_right`?
-- see Note [lower instance priority]

