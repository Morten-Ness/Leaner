import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem mul_finsum' {R : Type*} [NonUnitalNonAssocSemiring R] (f : α → R) (r : R)
    (h : HasFiniteSupport f) : (r * ∑ᶠ a : α, f a) = ∑ᶠ a : α, r * f a := (AddMonoidHom.mulLeft r).map_finsum h

