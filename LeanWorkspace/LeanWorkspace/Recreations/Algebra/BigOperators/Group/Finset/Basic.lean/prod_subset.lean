import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_subset (h : s₁ ⊆ s₂) (hf : ∀ x ∈ s₂, x ∉ s₁ → f x = 1) :
    ∏ x ∈ s₁, f x = ∏ x ∈ s₂, f x := haveI := Classical.decEq ι
  Finset.prod_subset_one_on_sdiff h (by simpa) fun _ _ => rfl

