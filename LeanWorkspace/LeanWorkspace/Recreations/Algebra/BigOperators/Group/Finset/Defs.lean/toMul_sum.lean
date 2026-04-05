import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [CommMonoid M]

theorem toMul_sum (s : Finset ι) (f : ι → Additive M) :
    (∑ i ∈ s, f i).toMul = ∏ i ∈ s, (f i).toMul := rfl

