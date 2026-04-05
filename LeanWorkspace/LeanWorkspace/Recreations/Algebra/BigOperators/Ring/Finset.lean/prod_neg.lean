import Mathlib

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

theorem prod_neg [CommMonoid M] [HasDistribNeg M] (f : ι → M) :
    ∏ x ∈ s, -f x = (-1) ^ #s * ∏ x ∈ s, f x := by
  simpa using (s.1.map f).prod_map_neg

