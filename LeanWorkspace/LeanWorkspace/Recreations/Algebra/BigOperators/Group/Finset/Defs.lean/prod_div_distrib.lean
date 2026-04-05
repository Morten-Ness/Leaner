import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [DivisionCommMonoid G]

theorem prod_div_distrib (f g : ι → G) : ∏ x ∈ s, f x / g x = (∏ x ∈ s, f x) / ∏ x ∈ s, g x := Multiset.prod_map_div

