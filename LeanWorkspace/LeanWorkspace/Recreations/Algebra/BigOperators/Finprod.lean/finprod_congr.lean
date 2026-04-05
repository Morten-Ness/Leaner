import Mathlib

variable {G M N : Type*} {α β ι : Sort*} [CommMonoid M] [CommMonoid N]

theorem finprod_congr {f g : α → M} (h : ∀ x, f x = g x) : finprod f = finprod g := congr_arg _ <| funext h

