import Mathlib

variable {α β : Type*}

variable [LinearOrder α] [CommSemigroup β]

theorem fn_max_mul_fn_min (f : α → β) (a b : α) : f (max a b) * f (min a b) = f a * f b := by
  grind

