import Mathlib

variable {α : Type*}

variable [Monoid α] {a b c : α} {m n : ℕ}

theorem dvd_pow (hab : a ∣ b) : ∀ {n : ℕ} (_ : n ≠ 0), a ∣ b ^ n
  | 0, hn => (hn rfl).elim
  | n + 1, _ => by rw [pow_succ']; exact hab.mul_right _

alias Dvd.dvd.pow := dvd_pow

