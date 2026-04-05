import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [Div α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

theorem iUnion₂_div (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋃ (i) (j), s i j) / t = ⋃ (i) (j), s i j / t := image2_iUnion₂_left ..

