import Mathlib

variable {α : Type*}

variable [AddCommMonoid α] [LinearOrder α] [CanonicallyOrderedAdd α] [Sub α] [OrderedSub α]
  {a b c : α}

theorem tsub_lt_self (ha : AddLECancellable a) (h₁ : 0 < a) (h₂ : 0 < b) : a - b < a := by
  refine tsub_le_self.lt_of_ne fun h => ?_
  rw [← h, tsub_pos_iff_lt] at h₁
  exact h₂.not_ge (ha.add_le_iff_nonpos_left.1 <| add_le_of_le_tsub_left_of_le h₁.le h.ge)

