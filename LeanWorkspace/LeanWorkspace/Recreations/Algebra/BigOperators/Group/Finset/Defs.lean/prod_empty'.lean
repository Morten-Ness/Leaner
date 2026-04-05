import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [CommMonoid M]

theorem prod_empty' : Finset.prod (∅ : Finset ι) = fun (_ : ι → M) => 1 := rfl

