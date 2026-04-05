import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_pow (hf : HasFiniteMulSupport f) (n : ℕ) : (∏ᶠ i, f i) ^ n = ∏ᶠ i, f i ^ n := map_finprod (powMonoidHom n) hf

