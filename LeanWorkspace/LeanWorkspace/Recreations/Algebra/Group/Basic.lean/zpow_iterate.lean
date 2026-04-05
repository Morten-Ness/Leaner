import Mathlib

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem zpow_iterate (k : ℤ) : ∀ n : ℕ, (fun x : G ↦ x ^ k)^[n] = (· ^ k ^ n)
  | 0 => by ext; simp [Int.pow_zero]
  | n + 1 => by ext; simp [zpow_iterate, Int.pow_succ', zpow_mul]
