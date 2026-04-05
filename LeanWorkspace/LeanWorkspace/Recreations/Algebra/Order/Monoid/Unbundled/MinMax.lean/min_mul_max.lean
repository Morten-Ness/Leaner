import Mathlib

variable {α β : Type*}

variable [LinearOrder α] [CommSemigroup β]

variable [CommSemigroup α]

theorem min_mul_max (a b : α) : min a b * max a b = a * b := fn_min_mul_fn_max id _ _

