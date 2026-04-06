import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [CommMonoid M]

theorem prod_toList {M : Type*} [CommMonoid M] (s : Finset M) :
    s.toList.prod = ∏ x ∈ s, x := by
  classical
  rw [Finset.prod_toList]
