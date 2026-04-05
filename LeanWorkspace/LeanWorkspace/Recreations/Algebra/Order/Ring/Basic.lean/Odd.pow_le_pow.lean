import Mathlib

variable {α M R : Type*}

variable [Semiring R] [LinearOrder R] [IsStrictOrderedRing R] {a b : R} {m n : ℕ}

variable [ExistsAddOfLE R]

theorem Odd.pow_le_pow {n : ℕ} (hn : Odd n) {a b : R} : a ^ n ≤ b ^ n ↔ a ≤ b := hn.strictMono_pow.le_iff_le

