import Mathlib

variable {ι M : Type*}

variable [CommMonoid M] {n : ℕ}

theorem prod_univ_two' (f : ι → M) (a b : ι) : ∏ i, f (![a, b] i) = f a * f b := Fin.prod_univ_two _

