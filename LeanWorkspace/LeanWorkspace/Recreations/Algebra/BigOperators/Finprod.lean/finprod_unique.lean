import Mathlib

variable {G M N : Type*} {α β ι : Sort*} [CommMonoid M] [CommMonoid N]

theorem finprod_unique [Unique α] (f : α → M) : ∏ᶠ i, f i = f default := finprod_eq_single f default fun _x hx => (hx <| Unique.eq_default _).elim

