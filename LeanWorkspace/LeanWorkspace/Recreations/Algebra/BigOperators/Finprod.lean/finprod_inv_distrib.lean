import Mathlib

variable {G M N : Type*} {α β ι : Sort*} [CommMonoid M] [CommMonoid N]

theorem finprod_inv_distrib [DivisionCommMonoid G] (f : α → G) : (∏ᶠ x, (f x)⁻¹) = (∏ᶠ x, f x)⁻¹ := ((MulEquiv.inv G).map_finprod f).symm

