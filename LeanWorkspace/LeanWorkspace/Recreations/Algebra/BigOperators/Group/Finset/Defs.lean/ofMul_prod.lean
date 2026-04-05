import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [CommMonoid M]

theorem ofMul_prod (s : Finset ι) (f : ι → M) : ofMul (∏ i ∈ s, f i) = ∑ i ∈ s, ofMul (f i) := rfl

