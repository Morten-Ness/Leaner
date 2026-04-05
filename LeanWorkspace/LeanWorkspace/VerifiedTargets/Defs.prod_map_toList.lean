import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [CommMonoid M]

theorem prod_map_toList (s : Finset ι) (f : ι → M) : (s.toList.map f).prod = s.prod f := by
  rw [Finset.prod, ← Multiset.prod_coe, ← Multiset.map_coe, Finset.coe_toList]

