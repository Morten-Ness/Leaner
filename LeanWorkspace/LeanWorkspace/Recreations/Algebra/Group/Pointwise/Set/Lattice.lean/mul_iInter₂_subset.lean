import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [Mul α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

theorem mul_iInter₂_subset (s : Set α) (t : ∀ i, κ i → Set α) :
    (s * ⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), s * t i j := image2_iInter₂_subset_right ..

