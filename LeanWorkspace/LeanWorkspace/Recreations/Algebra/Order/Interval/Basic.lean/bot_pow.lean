import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [CommMonoid α] [Preorder α] [IsOrderedMonoid α] (s : Interval α) {n : ℕ}

theorem bot_pow : ∀ {n : ℕ}, n ≠ 0 → (⊥ : Interval α) ^ n = ⊥
  | 0, h => (h rfl).elim
  | Nat.succ n, _ => Interval.mul_bot (⊥ ^ n)
