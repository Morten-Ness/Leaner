import Mathlib

open scoped Function -- required for scoped `on` notation

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

theorem degree_map_eq_iff {f : R →+* S} {p : Polynomial R} :
    degree (map f p) = degree p ↔ f (leadingCoeff p) ≠ 0 ∨ p = 0 := by
  rcases eq_or_ne p 0 with h | h
  · simp [h]
  simp only [h, or_false]
  refine ⟨fun h2 ↦ ?_, degree_map_eq_of_leadingCoeff_ne_zero f⟩
  have h3 : natDegree (map f p) = natDegree p := by simp_rw [natDegree, h2]
  have h4 : map f p ≠ 0 := by
    rwa [ne_eq, ← degree_eq_bot, h2, degree_eq_bot]
  rwa [← coeff_natDegree, ← coeff_map, ← h3, coeff_natDegree, ne_eq, leadingCoeff_eq_zero]

