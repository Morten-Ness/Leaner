import Mathlib

variable {F α β γ : Type*}

variable [Monoid α] {s t : Set α} {a : α} {m n : ℕ}

theorem prod_pow [Monoid β] (s : Set α) (t : Set β) : ∀ n, (s ×ˢ t) ^ n = (s ^ n) ×ˢ (t ^ n)
  | 0 => by simp
  | n + 1 => by simp [pow_succ, prod_pow _ _ n]
