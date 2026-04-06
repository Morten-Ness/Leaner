import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [CommMonoid M]

theorem prod_map_toList (s : Finset ι) (f : ι → M) : (s.toList.map f).prod = s.prod f := by
  simpa using Finset.prod_toList (s := s) (f := f)
