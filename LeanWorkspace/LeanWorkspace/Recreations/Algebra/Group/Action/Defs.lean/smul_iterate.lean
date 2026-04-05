import Mathlib

variable {M N G H α β γ δ : Type*}

variable [Monoid M] [MulAction M α] {a : M}

theorem smul_iterate (a : M) : ∀ n : ℕ, (a • · : α → α)^[n] = (a ^ n • ·)
  | 0 => by simp [funext_iff]
  | n + 1 => by ext; simp [smul_iterate, pow_succ, smul_smul]
