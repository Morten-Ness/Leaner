import Mathlib

variable {M N S : Type*}

variable [Monoid M] {a : M}

theorem pow (n : ℕ) (h : IsIdempotentElem a) : IsIdempotentElem (a ^ n) := Nat.recOn n ((pow_zero a).symm ▸ IsIdempotentElem.one) fun n _ =>
    show a ^ n.succ * a ^ n.succ = a ^ n.succ by
      conv_rhs => rw [← IsIdempotentElem.eq h]
      rw [← sq, ← sq, ← pow_mul, ← pow_mul']

