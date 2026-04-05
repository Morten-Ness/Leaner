import Mathlib

variable {F α β : Type*}

variable [Semiring α] [Semiring β] {a b : α} {m n : ℕ}

theorem Even.odd_add (ha : Even a) (hb : Odd b) : Odd (b + a) := add_comm a b ▸ ha.add_odd hb

