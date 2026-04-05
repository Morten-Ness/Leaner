import Mathlib

variable {α : Type*} [LinearOrder α] {P : α → Prop} {a b c : α}

variable [AddCommMagma α] [CanonicallyOrderedAdd α]

theorem le_add_iff_lt_right_or_exists_le [AddLeftMono α] [IsLeftCancelAdd α] :
    a ≤ b + c ↔ a < c ∨ ∃ d ≤ b, a = d + c := by
  rw [add_comm, le_add_iff_lt_left_or_exists_le]
  simp_rw [add_comm]

