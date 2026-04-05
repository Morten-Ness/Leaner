import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [LinearOrder M₀] [PosMulStrictMono M₀] {a b : M₀}
  {m n : ℕ}

variable [MulPosMono M₀]

theorem lt_of_mul_self_lt_mul_self₀ (hb : 0 ≤ b) : a * a < b * b → a < b := by
  simp only [← sq]
  exact lt_of_pow_lt_pow_left₀ _ hb

