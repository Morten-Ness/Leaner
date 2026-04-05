import Mathlib

variable {α M R : Type*}

variable [Semiring R] [LinearOrder R] [IsStrictOrderedRing R] {a b : R} {m n : ℕ}

variable [ExistsAddOfLE R]

theorem Odd.pow_inj {n : ℕ} (hn : Odd n) {a b : R} : a ^ n = b ^ n ↔ a = b := hn.pow_injective.eq_iff

