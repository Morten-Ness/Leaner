import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [DivisionCommMonoid G]

theorem prod_inv_distrib (f : ι → G) : (∏ x ∈ s, (f x)⁻¹) = (∏ x ∈ s, f x)⁻¹ := Multiset.prod_map_inv

