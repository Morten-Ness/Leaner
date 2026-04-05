import Mathlib

variable {M : Type*}

theorem prime_pow_iff [CommMonoidWithZero M] [IsCancelMulZero M] {p : M} {n : ℕ} :
    Prime (p ^ n) ↔ Prime p ∧ n = 1 := by
  refine ⟨fun hp ↦ ?_, fun ⟨hp, hn⟩ ↦ by simpa [hn]⟩
  suffices n = 1 by simp_all
  grind [not_prime_pow, Nat.zero_eq_one_mod_iff]

