import Mathlib

variable {ι : Type*}

theorem odd_sum_iff_odd_card_odd {s : Finset ι} (f : ι → ℕ) :
    Odd (∑ i ∈ s, f i) ↔ Odd #{x ∈ s | Odd (f x)} := by
  simp only [← Nat.not_even_iff_odd, Finset.even_sum_iff_even_card_odd]

