import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem Nat.cast_finsum_mem {s : Set ι} (hs : s.Finite) {M : Type*}
    [AddCommMonoidWithOne M] (f : ι → ℕ) : ↑(∑ᶠ x ∈ s, f x : ℕ) = ∑ᶠ x ∈ s, (f x : M) := (Nat.castAddMonoidHom M).map_finsum_mem _ hs

