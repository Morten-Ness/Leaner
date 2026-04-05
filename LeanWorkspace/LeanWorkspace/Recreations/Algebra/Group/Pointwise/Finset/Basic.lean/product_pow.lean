import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [Monoid α] {s t : Finset α} {a : α} {m n : ℕ}

theorem product_pow [Monoid β] (s : Finset α) (t : Finset β) : ∀ n, (s ×ˢ t) ^ n = (s ^ n) ×ˢ (t ^ n)
  | 0 => by simp
  | n + 1 => by simp [pow_succ, product_pow _ _ n]
