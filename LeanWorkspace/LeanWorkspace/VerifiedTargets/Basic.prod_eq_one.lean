import Mathlib

variable {F ι κ G M N O : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem prod_eq_one (h : ∀ x ∈ s, x = (1 : M)) : s.prod = 1 := by
  induction s using Quotient.inductionOn; simp [List.prod_eq_one h]

