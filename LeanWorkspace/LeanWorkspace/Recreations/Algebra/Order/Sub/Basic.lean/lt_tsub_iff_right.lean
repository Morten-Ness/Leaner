import Mathlib

variable {α : Type*}

variable [AddCommMonoid α] [LinearOrder α] [CanonicallyOrderedAdd α] [Sub α] [OrderedSub α]
  {a b c : α}

omit [CanonicallyOrderedAdd α] in
theorem lt_tsub_iff_right (hc : AddLECancellable c) : a < b - c ↔ a + c < b := ⟨lt_imp_lt_of_le_imp_le tsub_le_iff_right.mpr, hc.lt_tsub_of_add_lt_right⟩

