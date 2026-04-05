import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem Nat.cast_finsum [Finite ι] {M : Type*} [AddCommMonoidWithOne M]
    (f : ι → ℕ) : ↑(∑ᶠ x, f x : ℕ) = ∑ᶠ x, (f x : M) := (Nat.castAddMonoidHom M).map_finsum f.support.toFinite

