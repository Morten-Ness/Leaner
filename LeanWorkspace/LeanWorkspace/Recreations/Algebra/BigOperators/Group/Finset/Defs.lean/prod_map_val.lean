import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

theorem prod_map_val [CommMonoid M] (s : Finset ι) (f : ι → M) : (s.1.map f).prod = ∏ a ∈ s, f a := rfl

