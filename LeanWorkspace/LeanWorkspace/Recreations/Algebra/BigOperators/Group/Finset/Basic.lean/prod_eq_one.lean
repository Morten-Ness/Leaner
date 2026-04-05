import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_eq_one (h : ∀ x ∈ s, f x = 1) : ∏ x ∈ s, f x = 1 := calc
  ∏ x ∈ s, f x = ∏ _x ∈ s, 1 := Finset.prod_congr rfl h
  _ = 1 := prod_const_one

