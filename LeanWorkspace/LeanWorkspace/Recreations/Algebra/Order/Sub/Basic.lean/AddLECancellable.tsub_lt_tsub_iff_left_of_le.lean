import Mathlib

variable {α : Type*}

variable [AddCommMonoid α] [LinearOrder α] [CanonicallyOrderedAdd α] [Sub α] [OrderedSub α]
  {a b c : α}

theorem tsub_lt_tsub_iff_left_of_le (ha : AddLECancellable a) (hb : AddLECancellable b)
    (h : b ≤ a) : a - b < a - c ↔ c < b := lt_iff_lt_of_le_iff_le <| AddLECancellable.tsub_le_tsub_iff_left ha hb h

