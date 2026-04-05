import Mathlib

variable {α β : Type*}

variable [LinearOrder α] [CommSemigroup β]

variable [CommSemigroup α]

theorem max_mul_min (a b : α) : max a b * min a b = a * b := fn_max_mul_fn_min id _ _

