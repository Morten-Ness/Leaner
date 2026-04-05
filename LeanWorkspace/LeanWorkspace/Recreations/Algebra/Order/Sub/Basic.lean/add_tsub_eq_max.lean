import Mathlib

variable {α : Type*}

variable [AddCommMonoid α] [LinearOrder α] [CanonicallyOrderedAdd α] [Sub α] [OrderedSub α]
  {a b c : α}

theorem add_tsub_eq_max : a + (b - a) = max a b := by rw [add_comm, max_comm, tsub_add_eq_max]

