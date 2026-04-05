import Mathlib

variable {α : Type*} [LinearOrder α] {P : α → Prop} {a b c : α}

variable [Add α] [CanonicallyOrderedAdd α]

theorem forall_le_add_iff_le_left [AddLeftMono α] [IsLeftCancelAdd α] :
    (∀ a ≤ b + c, P a) ↔ (∀ a < b, P a) ∧ (∀ d ≤ c, P (b + d)) := by
  simp_rw [le_add_iff_lt_left_or_exists_le]
  aesop

