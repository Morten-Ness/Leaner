import Mathlib

variable {R : Type*}

variable {α : Type*} [CommMonoidWithZero α] [GCDMonoid α]

theorem Squarefree.gcd_left {a : α} (b : α) (ha : Squarefree a) : Squarefree (gcd a b) := ha.squarefree_of_dvd (gcd_dvd_left _ _)

