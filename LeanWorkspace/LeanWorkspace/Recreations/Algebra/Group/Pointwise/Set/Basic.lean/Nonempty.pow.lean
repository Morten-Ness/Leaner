import Mathlib

variable {F α β γ : Type*}

variable [Monoid α] {s t : Set α} {a : α} {m n : ℕ}

theorem Nonempty.pow (hs : s.Nonempty) : ∀ {n}, (s ^ n).Nonempty
  | 0 => by simp
  | n + 1 => by rw [pow_succ]; exact hs.pow.mul hs
