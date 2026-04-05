import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_cond_eq_right : (∏ᶠ (i) (_ : a = i), f i) = f a := by simp [@eq_comm _ a]

