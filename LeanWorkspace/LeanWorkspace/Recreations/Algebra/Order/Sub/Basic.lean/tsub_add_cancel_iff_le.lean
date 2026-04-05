import Mathlib

variable {α : Type*}

variable [AddCommMonoid α] [PartialOrder α] [CanonicallyOrderedAdd α]
  [Sub α] [OrderedSub α] {a b c : α}

theorem tsub_add_cancel_iff_le : b - a + a = b ↔ a ≤ b := by
  rw [add_comm]
  exact add_tsub_cancel_iff_le

-- This was previously a `@[simp]` lemma, but it is not necessarily a good idea, e.g. in
-- `example (h : n - m = 0) : a + (n - m) = a := by simp_all`

