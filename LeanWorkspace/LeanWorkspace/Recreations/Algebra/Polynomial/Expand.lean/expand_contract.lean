import Mathlib

open scoped Polynomial

variable (R : Type u) [CommSemiring R] {S : Type v} [CommSemiring S] (p q : ℕ)

theorem expand_contract [CharP R p] [NoZeroDivisors R] {f : R[X]} (hf : Polynomial.derivative f = 0)
    (hp : p ≠ 0) : Polynomial.expand R p (Polynomial.contract p f) = f := by
  ext n
  rw [Polynomial.coeff_expand hp.bot_lt, Polynomial.coeff_contract hp]
  split_ifs with h
  · rw [Nat.div_mul_cancel h]
  · rcases n with - | n
    · exact absurd (dvd_zero p) h
    have := coeff_derivative f n
    rw [hf, coeff_zero, zero_eq_mul] at this
    rcases this with h' | _
    · rw [h']
    rename_i _ _ _ h'
    rw [← Nat.cast_succ, CharP.cast_eq_zero_iff R p] at h'
    exact absurd h' h

