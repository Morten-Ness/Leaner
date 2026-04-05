import Mathlib

variable {R : Type*}

variable {p q : R}

theorem pow_succ_eq [Monoid R] [Star R] (hp : IsStarProjection p) (n : ℕ) : p ^ (n + 1) = p := hp.isIdempotentElem.pow_succ_eq n

