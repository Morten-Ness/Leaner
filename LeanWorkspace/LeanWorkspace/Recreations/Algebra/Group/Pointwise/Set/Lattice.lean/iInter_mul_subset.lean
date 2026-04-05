import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [Mul α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

theorem iInter_mul_subset (s : ι → Set α) (t : Set α) : (⋂ i, s i) * t ⊆ ⋂ i, s i * t := Set.image2_iInter_subset_left ..

