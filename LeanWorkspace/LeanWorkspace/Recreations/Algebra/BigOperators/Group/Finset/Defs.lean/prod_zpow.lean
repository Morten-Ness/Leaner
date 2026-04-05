import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [DivisionCommMonoid G]

theorem prod_zpow (f : ι → G) (s : Finset ι) (n : ℤ) : ∏ a ∈ s, f a ^ n = (∏ a ∈ s, f a) ^ n := Multiset.prod_map_zpow

