import Mathlib

variable {ι α β M N G k R : Type*}

variable [DecidableEq β]

theorem mul_card_image_le_card_of_maps_to {f : α → β} {s : Finset α} {t : Finset β}
    (Hf : ∀ a ∈ s, f a ∈ t) (n : ℕ) (hn : ∀ b ∈ t, n ≤ #{a ∈ s | f a = b}) :
    n * #t ≤ #s := calc
    n * #t = ∑ _a ∈ t, n := by simp [mul_comm]
    _ ≤ ∑ b ∈ t, #{a ∈ s | f a = b} := sum_le_sum hn
    _ = #s := by rw [← card_eq_sum_card_fiberwise Hf]

