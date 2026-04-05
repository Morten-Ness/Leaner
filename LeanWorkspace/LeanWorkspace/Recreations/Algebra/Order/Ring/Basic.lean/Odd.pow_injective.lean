import Mathlib

variable {α M R : Type*}

variable [Semiring R] [LinearOrder R] [IsStrictOrderedRing R] {a b : R} {m n : ℕ}

variable [ExistsAddOfLE R]

theorem Odd.pow_injective {n : ℕ} (hn : Odd n) : Function.Injective (· ^ n : R → R) := hn.strictMono_pow.injective

