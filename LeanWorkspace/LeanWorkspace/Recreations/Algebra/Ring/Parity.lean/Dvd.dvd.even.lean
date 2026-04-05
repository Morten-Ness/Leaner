import Mathlib

variable {F α β : Type*}

variable [Semiring α] [Semiring β] {a b : α} {m n : ℕ}

theorem Dvd.dvd.even (hab : a ∣ b) (ha : Even a) : Even b := ha.trans_dvd hab

