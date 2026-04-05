import Mathlib

variable {α β γ : Type*}

variable {s : Finset α} {a : α}

variable [CommMonoid β]

theorem prod_powersetCard (n : ℕ) (s : Finset α) (f : ℕ → β) :
    ∏ t ∈ powersetCard n s, f #t = f n ^ (#s).choose n := by
  rw [prod_eq_pow_card, card_powersetCard]; rintro a ha; rw [(mem_powersetCard.1 ha).2]

