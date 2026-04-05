import Mathlib

variable {α : Type*}

theorem compare_val [Monoid α] [Ord α] (a b : αˣ) : compare a.val b.val = compare a b := rfl

