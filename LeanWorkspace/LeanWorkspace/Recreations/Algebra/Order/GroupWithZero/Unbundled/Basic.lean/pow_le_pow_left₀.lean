import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [Preorder M₀] {a b : M₀} {m n : ℕ}

theorem pow_le_pow_left₀ [PosMulMono M₀] [MulPosMono M₀]
    (ha : 0 ≤ a) (hab : a ≤ b) : ∀ n, a ^ n ≤ b ^ n
  | 0 => by simp
  | 1 => by simpa using hab
  | n + 2 => by simpa only [pow_succ']
      using mul_le_mul hab (pow_le_pow_left₀ ha hab _) (pow_succ_nonneg ha _) (ha.trans hab)
