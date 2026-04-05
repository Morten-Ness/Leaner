import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [Monoid α] {s t : Finset α} {a : α} {m n : ℕ}

theorem singleton_pow (a : α) : ∀ n, ({a} : Finset α) ^ n = {a ^ n}
  | 0 => by simp [Finset.singleton_one]
  | n + 1 => by simp [pow_succ, singleton_pow _ n]
