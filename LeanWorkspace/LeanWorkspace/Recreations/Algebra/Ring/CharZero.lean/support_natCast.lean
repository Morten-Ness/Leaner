import Mathlib

variable {α R S : Type*} {n : ℕ}

variable [AddMonoidWithOne R] [CharZero R]

theorem support_natCast (hn : n ≠ 0) : support (n : α → R) = Set.univ := support_const <| Nat.cast_ne_zero.2 hn

