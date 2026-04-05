import Mathlib

variable {α : Type*} [LinearOrder α] {P : α → Prop} {a b c : α}

variable [Add α] [CanonicallyOrderedAdd α]

theorem forall_lt_add_iff_lt_left [AddLeftReflectLT α] [IsLeftCancelAdd α] :
    (∀ a < b + c, P a) ↔ (∀ a < b, P a) ∧ (∀ d < c, P (b + d)) := by
  simp_rw [lt_add_iff_lt_left_or_exists_lt]
  aesop

