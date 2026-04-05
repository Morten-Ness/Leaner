import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [Preorder M₀] {a b : M₀} {m n : ℕ}

theorem pow_lt_one₀ [PosMulMono M₀] (h₀ : 0 ≤ a) (h₁ : a < 1) : ∀ {n : ℕ}, n ≠ 0 → a ^ n < 1
  | 0, h => (h rfl).elim
  | n + 1, _ => by
    rw [pow_succ']; exact mul_lt_one_of_nonneg_of_lt_one_left h₀ h₁ (pow_le_one₀ h₀ h₁.le)
