import Mathlib

variable {F α β γ : Type*}

variable [DivisionMonoid α] {s t : Set α} {n : ℤ}

theorem Nonempty.zpow (hs : s.Nonempty) : ∀ {n : ℤ}, (s ^ n).Nonempty
  | (n : ℕ) => hs.pow
  | .negSucc n => by simpa using hs.pow
