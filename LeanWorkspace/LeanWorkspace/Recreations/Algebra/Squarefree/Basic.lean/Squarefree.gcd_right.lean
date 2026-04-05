import Mathlib

variable {R : Type*}

variable {α : Type*} [CommMonoidWithZero α] [GCDMonoid α]

theorem Squarefree.gcd_right (a : α) {b : α} (hb : Squarefree b) : Squarefree (gcd a b) := hb.squarefree_of_dvd (gcd_dvd_right _ _)

