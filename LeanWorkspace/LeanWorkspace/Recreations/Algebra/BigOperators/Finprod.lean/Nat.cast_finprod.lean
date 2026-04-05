import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem Nat.cast_finprod [Finite ι] {R : Type*} [CommSemiring R] (f : ι → ℕ) :
    ↑(∏ᶠ x, f x : ℕ) = ∏ᶠ x, (f x : R) := map_finprod (Nat.castRingHom R) f.mulSupport.toFinite

