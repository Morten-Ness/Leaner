import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_attach (s : Finset ι) (f : ι → M) : ∏ x ∈ s.attach, f x = ∏ x ∈ s, f x := by
  classical rw [← Finset.prod_image Subtype.coe_injective.injOn, attach_image_val]

