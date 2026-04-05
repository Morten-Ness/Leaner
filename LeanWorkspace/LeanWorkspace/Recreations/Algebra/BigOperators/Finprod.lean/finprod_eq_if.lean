import Mathlib

variable {G M N : Type*} {α β ι : Sort*} [CommMonoid M] [CommMonoid N]

theorem finprod_eq_if {p : Prop} [Decidable p] {x : M} : ∏ᶠ _ : p, x = if p then x else 1 := finprod_eq_dif fun _ => x

