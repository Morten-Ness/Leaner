import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [CommMonoid M]

theorem prod_const_one : (∏ _x ∈ s, (1 : M)) = 1 := by
  simp only [Finset.prod, Multiset.map_const', Multiset.prod_replicate, one_pow]

