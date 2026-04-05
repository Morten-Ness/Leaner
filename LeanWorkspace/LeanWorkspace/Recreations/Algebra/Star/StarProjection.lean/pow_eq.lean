import Mathlib

variable {R : Type*}

variable {p q : R}

theorem pow_eq [Monoid R] [Star R] (hp : IsStarProjection p) {n : ℕ} (hn : n ≠ 0) : p ^ n = p := hp.isIdempotentElem.pow_eq hn

