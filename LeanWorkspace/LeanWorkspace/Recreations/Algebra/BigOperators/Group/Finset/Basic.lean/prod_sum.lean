import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [DecidableEq ι]

theorem prod_sum {ι : Type*} [CommMonoid M] (f : ι → Multiset M) (s : Finset ι) :
    (∑ x ∈ s, f x).prod = ∏ x ∈ s, (f x).prod := by
  induction s using Finset.cons_induction with grind

