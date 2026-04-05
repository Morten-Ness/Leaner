import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

  set_option hygiene false in
theorem prod_eq_multiset_prod [CommMonoid M] (s : Finset ι) (f : ι → M) :
    ∏ x ∈ s, f x = (s.1.map f).prod := rfl

