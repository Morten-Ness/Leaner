import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [AddCommMonoid M]

theorem toAdd_prod (s : Finset ι) (f : ι → Multiplicative M) :
    (∏ i ∈ s, f i).toAdd = ∑ i ∈ s, (f i).toAdd := rfl

