import Mathlib

variable {α β G M : Type*}

variable [Monoid M] {a b : M} {m n : ℕ}

theorem pow_iterate (k : ℕ) : ∀ n : ℕ, (fun x : M ↦ x ^ k)^[n] = (· ^ k ^ n)
  | 0 => by ext; simp
  | n + 1 => by ext; simp [pow_iterate, Nat.pow_succ', pow_mul]
