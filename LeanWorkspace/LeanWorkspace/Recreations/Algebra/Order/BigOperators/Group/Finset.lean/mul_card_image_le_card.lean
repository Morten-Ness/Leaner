import Mathlib

variable {ι α β M N G k R : Type*}

variable [DecidableEq β]

theorem mul_card_image_le_card {f : α → β} (s : Finset α) (n : ℕ)
    (hn : ∀ b ∈ s.image f, n ≤ #{a ∈ s | f a = b}) : n * #(s.image f) ≤ #s := Finset.mul_card_image_le_card_of_maps_to (fun _ ↦ mem_image_of_mem _) n hn

