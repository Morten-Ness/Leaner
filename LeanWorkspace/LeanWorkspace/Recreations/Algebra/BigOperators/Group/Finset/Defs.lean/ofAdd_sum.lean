import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [AddCommMonoid M]

theorem ofAdd_sum (s : Finset ι) (f : ι → M) : ofAdd (∑ i ∈ s, f i) = ∏ i ∈ s, ofAdd (f i) := rfl

