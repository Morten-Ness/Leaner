import Mathlib

variable {α R S : Type*} {n : ℕ}

variable [AddMonoidWithOne R] [CharZero R]

theorem mulSupport_natCast (hn : n ≠ 1) : mulSupport (n : α → R) = Set.univ := mulSupport_const <| Nat.cast_ne_one.2 hn

