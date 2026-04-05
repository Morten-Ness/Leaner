import Mathlib

variable {α β γ : Type*}

variable {M G : Type*}

variable [AddMonoid M]

theorem log_pow : ∀ (x : Mᵐ⁰) (n : ℕ), WithZero.log (x ^ n) = n • WithZero.log x
  | 0, 0 => by simp
  | 0, n + 1 => by simp
  | (x : Multiplicative M), n => rfl
