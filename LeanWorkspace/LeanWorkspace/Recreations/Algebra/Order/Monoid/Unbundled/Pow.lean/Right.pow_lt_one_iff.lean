import Mathlib

variable {β G M : Type*}

variable [Monoid M]

variable [LinearOrder M]

theorem Right.pow_lt_one_iff [MulRightStrictMono M] {n : ℕ} {x : M}
    (hn : 0 < n) : x ^ n < 1 ↔ x < 1 := haveI := mulRightMono_of_mulRightStrictMono M
  ⟨fun H => not_le.mp fun k => H.not_ge <| Right.one_le_pow_of_le k, Right.pow_lt_one_of_lt hn⟩

