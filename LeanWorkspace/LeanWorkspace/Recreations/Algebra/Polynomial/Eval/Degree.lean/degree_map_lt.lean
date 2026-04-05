import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S] {f : R →+* S} {p : R[X]}

theorem degree_map_lt (hp : f p.leadingCoeff = 0) (hp₀ : p ≠ 0) : (p.map f).degree < p.degree := by
  refine Polynomial.degree_map_le.lt_of_ne fun hpq ↦ hp₀ ?_
  rw [leadingCoeff, ← coeff_map, ← natDegree_eq_natDegree hpq, ← leadingCoeff, leadingCoeff_eq_zero]
    at hp
  rw [← degree_eq_bot, ← hpq, hp, degree_zero]

