import Mathlib

variable {α : Type*}

variable [AddCommMonoid α] [LinearOrder α] [CanonicallyOrderedAdd α] [Sub α] [OrderedSub α]
  {a b c : α}

theorem tsub_lt_self_iff (ha : AddLECancellable a) : a - b < a ↔ 0 < a ∧ 0 < b := by
  refine
    ⟨fun h => ⟨(zero_le _).trans_lt h, (zero_le b).lt_of_ne ?_⟩, fun h => AddLECancellable.tsub_lt_self ha h.1 h.2⟩
  rintro rfl
  rw [tsub_zero] at h
  exact h.false

