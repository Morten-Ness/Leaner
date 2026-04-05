import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [SMul α β] {s s₁ s₂ : Set α} {t t₁ t₂ u : Set β} {a : α}
  {b : β}

theorem iUnion₂_smul (s : ∀ i, κ i → Set α) (t : Set β) :
    (⋃ i, ⋃ j, s i j) • t = ⋃ i, ⋃ j, s i j • t := image2_iUnion₂_left ..

