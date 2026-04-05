import Mathlib

variable {F α β : Type*}

variable [Semiring α] [Semiring β] {a b : α} {m n : ℕ}

theorem Odd.natCast {R : Type*} [Semiring R] {n : ℕ} (hn : Odd n) : Odd (n : R) := hn.map <| Nat.castRingHom R

