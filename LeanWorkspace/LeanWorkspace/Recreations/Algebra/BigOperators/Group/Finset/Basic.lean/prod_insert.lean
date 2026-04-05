import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_insert [DecidableEq ι] : a ∉ s → ∏ x ∈ insert a s, f x = f a * ∏ x ∈ s, f x := fold_insert

