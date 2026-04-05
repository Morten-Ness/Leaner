import Mathlib

variable {α : Type*} [LinearOrder α] {P : α → Prop} {a b c : α}

variable [AddCommMagma α] [CanonicallyOrderedAdd α]

theorem lt_add_iff_lt_right_or_exists_lt [AddLeftReflectLT α] [IsLeftCancelAdd α] :
    a < b + c ↔ a < c ∨ ∃ d < b, a = d + c := by
  rw [add_comm, lt_add_iff_lt_left_or_exists_lt]
  simp_rw [add_comm]

