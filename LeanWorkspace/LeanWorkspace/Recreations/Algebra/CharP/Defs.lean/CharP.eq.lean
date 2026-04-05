import Mathlib

variable (R : Type*)

variable [AddMonoidWithOne R] (p : ℕ)

variable [CharP R p] {a b : ℕ}

theorem eq {p q : ℕ} (hp : CharP R p) (hq : CharP R q) : p = q := Nat.dvd_antisymm ((cast_eq_zero_iff (self := hp) R p q).1 (@cast_eq_zero _ _ _ hq))
    ((cast_eq_zero_iff (self := hq) R q p).1 (@cast_eq_zero _ _ _ hp))

