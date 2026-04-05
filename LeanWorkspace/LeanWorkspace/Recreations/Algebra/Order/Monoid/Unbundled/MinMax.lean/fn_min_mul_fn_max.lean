import Mathlib

variable {α β : Type*}

variable [LinearOrder α] [CommSemigroup β]

theorem fn_min_mul_fn_max (f : α → β) (a b : α) : f (min a b) * f (max a b) = f a * f b := by
  grind

