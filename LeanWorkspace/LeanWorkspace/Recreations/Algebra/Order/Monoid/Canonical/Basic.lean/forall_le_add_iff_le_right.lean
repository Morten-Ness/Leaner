import Mathlib

variable {α : Type*} [LinearOrder α] {P : α → Prop} {a b c : α}

variable [AddCommMagma α] [CanonicallyOrderedAdd α]

theorem forall_le_add_iff_le_right [AddLeftMono α] [IsLeftCancelAdd α] :
    (∀ a ≤ b + c, P a) ↔ (∀ a < c, P a) ∧ (∀ d ≤ b, P (d + c)) := by
  simp_rw [le_add_iff_lt_right_or_exists_le]
  aesop

