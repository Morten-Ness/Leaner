import Mathlib

variable {α : Type*} [LinearOrder α] {P : α → Prop} {a b c : α}

variable [Add α] [CanonicallyOrderedAdd α]

theorem lt_add_iff_lt_left_or_exists_lt [AddLeftReflectLT α] [IsLeftCancelAdd α] :
    a < b + c ↔ a < b ∨ ∃ d < c, a = b + d := by
  obtain h | h := lt_or_ge a b
  · have : a < b + c := h.trans_le (le_self_add ..)
    tauto
  · obtain ⟨a, rfl⟩ := exists_add_of_le h
    simp

