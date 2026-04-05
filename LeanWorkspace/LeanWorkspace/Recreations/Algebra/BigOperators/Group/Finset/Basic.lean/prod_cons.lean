import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_cons (h : a ∉ s) : ∏ x ∈ cons a s h, f x = f a * ∏ x ∈ s, f x := fold_cons h

