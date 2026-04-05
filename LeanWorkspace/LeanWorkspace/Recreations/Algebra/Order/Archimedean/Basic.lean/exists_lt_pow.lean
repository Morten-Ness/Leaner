import Mathlib

variable {G M R K : Type*}

theorem exists_lt_pow [CommMonoid M] [PartialOrder M] [MulArchimedean M] [MulLeftStrictMono M]
    {a : M} (ha : 1 < a) (b : M) : ∃ n : ℕ, b < a ^ n := let ⟨k, hk⟩ := MulArchimedean.arch b ha
  ⟨k + 1, hk.trans_lt <| pow_lt_pow_right' ha k.lt_succ_self⟩

