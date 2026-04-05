import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R] {p p₁ p₂ q : R[X]}

theorem rootMultiplicity_eq_natTrailingDegree' : p.rootMultiplicity 0 = p.natTrailingDegree := by
  by_cases h : p = 0
  · simp only [h, Polynomial.rootMultiplicity_zero, natTrailingDegree_zero]
  refine le_antisymm ?_ ?_
  · rw [Polynomial.rootMultiplicity_le_iff h, map_zero, sub_zero, Polynomial.X_pow_dvd_iff, not_forall]
    exact ⟨p.natTrailingDegree,
      fun h' ↦ trailingCoeff_nonzero_iff_nonzero.2 h <| h' <| Nat.lt_add_one _⟩
  · rw [Polynomial.le_rootMultiplicity_iff h, map_zero, sub_zero, Polynomial.X_pow_dvd_iff]
    exact fun _ ↦ coeff_eq_zero_of_lt_natTrailingDegree

