import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_singleton (f : ι → M) (a : ι) : ∏ x ∈ singleton a, f x = f a := Eq.trans fold_singleton <| mul_one _

