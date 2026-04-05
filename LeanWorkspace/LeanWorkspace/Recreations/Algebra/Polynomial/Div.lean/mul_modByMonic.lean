import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R] {p p₁ p₂ q : R[X]}

theorem mul_modByMonic (p₁ p₂ q : R[X]) : (p₁ * p₂) %ₘ q = (p₁ %ₘ q) * (p₂ %ₘ q) %ₘ q := by
  by_cases! h : ¬ q.Monic
  · simp [Polynomial.modByMonic_eq_of_not_monic _ h]
  apply Polynomial.modByMonic_eq_of_dvd_sub h
  have : p₁ * p₂ - p₁ %ₘ q * (p₂ %ₘ q) = (p₁ %ₘ q) * (p₂ - p₂ %ₘ q) + p₂ * (p₁ - p₁ %ₘ q) := by ring
  rw [this]
  apply dvd_add
  all_goals
  · apply dvd_mul_of_dvd_right
    simp [Polynomial.modByMonic_eq_sub_mul_div]

