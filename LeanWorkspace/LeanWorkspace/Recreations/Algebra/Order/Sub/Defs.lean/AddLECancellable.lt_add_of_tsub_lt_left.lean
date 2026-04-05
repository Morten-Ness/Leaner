import Mathlib

variable {α : Type*}

variable [PartialOrder α] [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

theorem lt_add_of_tsub_lt_left (hb : AddLECancellable b) (h : a - b < c) : a < b + c := by
  rw [lt_iff_le_and_ne, ← tsub_le_iff_left]
  refine ⟨h.le, ?_⟩
  rintro rfl
  simp [hb] at h

