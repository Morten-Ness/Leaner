import Mathlib

variable {α : Type u}

variable [Monoid α] [LinearOrder α] [CanonicallyOrderedMul α]

theorem min_mul_distrib (a b c : α) : min a (b * c) = min a (min a b * min a c) := by
  rcases le_total a b with hb | hb
  · simp [hb, le_mul_right]
  · rcases le_total a c with hc | hc
    · simp [hc, le_mul_left]
    · simp [hb, hc]

