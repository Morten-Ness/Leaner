import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [Fintype ι] [Fintype κ]

variable [CommMonoid M]

theorem prod_empty [IsEmpty ι] (f : ι → M) : ∏ x : ι, f x = 1 := Finset.prod_of_isEmpty _

