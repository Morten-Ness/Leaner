import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem Nat.cast_finprod_mem {s : Set ι} (hs : s.Finite) {R : Type*} [CommSemiring R] (f : ι → ℕ) :
    ↑(∏ᶠ x ∈ s, f x : ℕ) = ∏ᶠ x ∈ s, (f x : R) := (Nat.castRingHom R).map_finprod_mem _ hs

