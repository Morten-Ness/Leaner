import Mathlib

variable {ι α β M N G k R : Type*}

variable [DecidableEq β]

theorem card_le_mul_card_image {f : α → β} (s : Finset α) (n : ℕ)
    (hn : ∀ b ∈ s.image f, #{a ∈ s | f a = b} ≤ n) : #s ≤ n * #(s.image f) := Finset.card_le_mul_card_image_of_maps_to (fun _ ↦ mem_image_of_mem _) n hn

