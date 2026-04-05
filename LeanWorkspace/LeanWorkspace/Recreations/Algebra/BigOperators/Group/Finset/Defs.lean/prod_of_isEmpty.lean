import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [CommMonoid M]

theorem prod_of_isEmpty [IsEmpty ι] (s : Finset ι) : ∏ i ∈ s, f i = 1 := by
  rw [eq_empty_of_isEmpty s, Finset.prod_empty]

