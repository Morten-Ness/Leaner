import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R] {p p₁ p₂ q : R[X]}

variable [IsDomain R]

theorem eq_of_dvd_of_natDegree_le_of_leadingCoeff {p q : R[X]} (hpq : p ∣ q)
    (h₁ : q.natDegree ≤ p.natDegree) (h₂ : p.leadingCoeff = q.leadingCoeff) :
    p = q := by
  rcases eq_or_ne q 0 with rfl | hq
  · simpa using h₂
  replace h₁ := (natDegree_le_of_dvd hpq hq).antisymm h₁
  obtain ⟨u, rfl⟩ := hpq
  rw [mul_ne_zero_iff] at hq
  rw [natDegree_mul hq.1 hq.2, left_eq_add] at h₁
  rw [eq_C_of_natDegree_eq_zero h₁, leadingCoeff_mul, leadingCoeff_C,
    eq_comm, mul_eq_left₀ (leadingCoeff_ne_zero.mpr hq.1)] at h₂
  rw [eq_C_of_natDegree_eq_zero h₁, h₂, map_one, mul_one]

