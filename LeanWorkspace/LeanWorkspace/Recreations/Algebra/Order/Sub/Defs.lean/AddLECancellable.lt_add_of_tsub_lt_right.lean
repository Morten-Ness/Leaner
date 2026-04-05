import Mathlib

variable {α : Type*}

variable [PartialOrder α] [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

theorem lt_add_of_tsub_lt_right (hc : AddLECancellable c) (h : a - c < b) :
    a < b + c := by
  rw [lt_iff_le_and_ne, ← tsub_le_iff_right]
  refine ⟨h.le, ?_⟩
  rintro rfl
  simp [hc] at h

