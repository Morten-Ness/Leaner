import Mathlib

variable {α β G M : Type*}

variable [DivisionMonoid α] {a b c d : α}

theorem zpow_neg (a : α) : ∀ n : ℤ, a ^ (-n) = (a ^ n)⁻¹
  | (_ + 1 : ℕ) => DivInvMonoid.zpow_neg' _ _
  | 0 => by simp
  | Int.negSucc n => by
    rw [zpow_negSucc, inv_inv, ← zpow_natCast]
    rfl
