import Mathlib

variable {F ι κ G M N O : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem prod_eq_pow_single [DecidableEq M] (a : M) (h : ∀ a' ≠ a, a' ∈ s → a' = 1) :
    s.prod = a ^ s.count a := by
  induction s using Quotient.inductionOn; simp [List.prod_eq_pow_single a h]

