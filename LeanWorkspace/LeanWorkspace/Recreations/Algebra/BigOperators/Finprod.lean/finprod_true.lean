import Mathlib

variable {G M N : Type*} {α β ι : Sort*} [CommMonoid M] [CommMonoid N]

theorem finprod_true (f : True → M) : ∏ᶠ i, f i = f trivial := @finprod_unique M True _ ⟨⟨trivial⟩, fun _ => rfl⟩ f

