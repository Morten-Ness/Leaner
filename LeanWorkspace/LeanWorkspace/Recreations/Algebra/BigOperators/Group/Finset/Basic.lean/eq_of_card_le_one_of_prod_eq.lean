import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem eq_of_card_le_one_of_prod_eq {s : Finset ι} (hc : #s ≤ 1) {f : ι → M} {b : M}
    (h : ∏ x ∈ s, f x = b) : ∀ x ∈ s, f x = b := by
  intro x hx
  by_cases hc0 : #s = 0
  · exact False.elim (card_ne_zero_of_mem hx hc0)
  · have h1 : #s = 1 := le_antisymm hc (Nat.one_le_of_lt (Nat.pos_of_ne_zero hc0))
    rw [card_eq_one] at h1
    grind

