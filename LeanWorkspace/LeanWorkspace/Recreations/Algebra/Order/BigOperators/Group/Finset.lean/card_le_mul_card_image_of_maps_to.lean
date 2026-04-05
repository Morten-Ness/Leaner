import Mathlib

variable {ι α β M N G k R : Type*}

variable [DecidableEq β]

theorem card_le_mul_card_image_of_maps_to {f : α → β} {s : Finset α} {t : Finset β}
    (Hf : ∀ a ∈ s, f a ∈ t) (n : ℕ) (hn : ∀ b ∈ t, #{a ∈ s | f a = b} ≤ n) : #s ≤ n * #t := calc
    #s = ∑ b ∈ t, #{a ∈ s | f a = b} := card_eq_sum_card_fiberwise Hf
    _ ≤ ∑ _b ∈ t, n := sum_le_sum hn
    _ = _ := by simp [mul_comm]

