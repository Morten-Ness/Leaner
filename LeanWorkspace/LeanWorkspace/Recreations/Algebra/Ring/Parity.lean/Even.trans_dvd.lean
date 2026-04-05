import Mathlib

variable {F α β : Type*}

variable [Semiring α] [Semiring β] {a b : α} {m n : ℕ}

theorem Even.trans_dvd (ha : Even a) (hab : a ∣ b) : Even b := even_iff_two_dvd.2 <| ha.two_dvd.trans hab

