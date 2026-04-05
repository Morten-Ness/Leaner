import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finsum_mul' {R : Type*} [NonUnitalNonAssocSemiring R] (f : α → R) (r : R)
    (h : HasFiniteSupport f) : (∑ᶠ a : α, f a) * r = ∑ᶠ a : α, f a * r := (AddMonoidHom.mulRight r).map_finsum h

