import Mathlib

variable {F α β γ : Type*}

variable [Monoid α] {s t : Set α} {a : α} {m n : ℕ}

theorem singleton_pow (a : α) : ∀ n, ({a} : Set α) ^ n = {a ^ n}
  | 0 => by simp [Set.singleton_one]
  | n + 1 => by simp [pow_succ, singleton_pow _ n]
