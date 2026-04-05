import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finsum_mem_mul' {R : Type*} [NonUnitalNonAssocSemiring R] {s : Set α} (f : α → R) (r : R)
    (hs : s.Finite) : (∑ᶠ a ∈ s, f a) * r = ∑ᶠ a ∈ s, f a * r := (AddMonoidHom.mulRight r).map_finsum_mem f hs

