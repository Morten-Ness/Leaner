import Mathlib

variable {F α β : Type*}

variable [Semiring α] [Semiring β] {a b : α} {m n : ℕ}

theorem Odd.add_even (ha : Odd a) (hb : Even b) : Odd (a + b) := add_comm a b ▸ hb.add_odd ha

