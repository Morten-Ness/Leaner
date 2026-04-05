import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_curry (f : α × β → M) (hf : HasFiniteMulSupport f) :
    ∏ᶠ ab, f ab = ∏ᶠ (a) (b), f (a, b) := by
  have h₁ : ∀ a, ∏ᶠ _ : a ∈ hf.toFinset, f a = f a := by simp
  have h₂ : ∏ᶠ a, f a = ∏ᶠ (a) (_ : a ∈ hf.toFinset), f a := by simp
  simp_rw [h₂, finprod_mem_finset_product, h₁]

