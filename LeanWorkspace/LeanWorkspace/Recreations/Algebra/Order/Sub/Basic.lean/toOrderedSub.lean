import Mathlib

variable {α : Type*}

variable [AddCommMonoid α] [LinearOrder α] [CanonicallyOrderedAdd α]

theorem toOrderedSub [AddRightReflectLE α] : OrderedSub α where
  tsub_le_iff_right a b c := by
    change dite _ _ _ ≤ c ↔ _
    split_ifs with h
    · have := (exists_add_of_le h).choose_spec
      rw [this] at h
      conv_rhs => rw [this, add_comm]
      rw [add_le_add_iff_right]
    · rw [not_le] at h
      constructor <;> intro h'
      · simpa using add_le_add h' h.le
      · exact zero_le c

