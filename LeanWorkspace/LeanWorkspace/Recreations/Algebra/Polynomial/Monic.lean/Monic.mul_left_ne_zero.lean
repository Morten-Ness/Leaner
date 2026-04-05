import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Semiring R] {p : R[X]}

theorem Monic.mul_left_ne_zero (hp : Polynomial.Monic p) {q : R[X]} (hq : q ≠ 0) : q * p ≠ 0 := by
  by_cases h : p = 1
  · simpa [h]
  rw [Ne, ← degree_eq_bot, hp.degree_mul, WithBot.add_eq_bot, not_or, degree_eq_bot]
  refine ⟨hq, ?_⟩
  rw [← Polynomial.Monic.degree_le_zero_iff_eq_one hp, not_le] at h
  refine (lt_trans ?_ h).ne'
  simp

