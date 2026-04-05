import Mathlib

variable {M N S : Type*}

variable [Monoid M] {a : M}

theorem pow_succ_eq (n : ℕ) (h : IsIdempotentElem a) : a ^ (n + 1) = a := Nat.recOn n ((Nat.zero_add 1).symm ▸ pow_one a) fun n ih => by rw [pow_succ, ih, IsIdempotentElem.eq h]

