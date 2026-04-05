import Mathlib

variable {α G M : Type*}

variable [CommMonoid M] {s₂ s₁ s : Finset α} {a : α} {g f : α → M}

theorem sum_range_id (n : ℕ) : ∑ i ∈ range n, i = n * (n - 1) / 2 := by
  rw [← Finset.sum_range_id_mul_two n, Nat.mul_div_cancel _ Nat.zero_lt_two]

