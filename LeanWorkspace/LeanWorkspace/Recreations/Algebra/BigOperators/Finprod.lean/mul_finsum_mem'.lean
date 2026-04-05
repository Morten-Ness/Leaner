import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem mul_finsum_mem' {R : Type*} [NonUnitalNonAssocSemiring R] {s : Set α} (f : α → R) (r : R)
    (hs : s.Finite) : (r * ∑ᶠ a ∈ s, f a) = ∑ᶠ a ∈ s, r * f a := (AddMonoidHom.mulLeft r).map_finsum_mem f hs

