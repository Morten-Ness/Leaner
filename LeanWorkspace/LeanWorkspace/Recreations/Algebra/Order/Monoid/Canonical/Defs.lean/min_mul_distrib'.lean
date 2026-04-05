import Mathlib

variable {α : Type u}

variable [Monoid α] [LinearOrder α] [CanonicallyOrderedMul α]

theorem min_mul_distrib' (a b c : α) : min (a * b) c = min (min a c * min b c) c := by
  simpa [min_comm _ c] using min_mul_distrib c a b

