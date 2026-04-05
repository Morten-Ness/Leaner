import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [CommMonoid M]

theorem prod_coe_sort_eq_attach (f : s → M) : ∏ i : s, f i = ∏ i ∈ s.attach, f i := rfl

