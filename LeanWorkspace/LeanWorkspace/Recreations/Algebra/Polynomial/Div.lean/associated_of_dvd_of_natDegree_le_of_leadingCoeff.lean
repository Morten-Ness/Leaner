import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R] {p p₁ p₂ q : R[X]}

variable [IsDomain R]

theorem associated_of_dvd_of_natDegree_le_of_leadingCoeff {p q : R[X]} (hpq : p ∣ q)
    (h₁ : q.natDegree ≤ p.natDegree) (h₂ : q.leadingCoeff ∣ p.leadingCoeff) :
    Associated p q := have ⟨r, hr⟩ := hpq
  have ⟨u, hu⟩ := associated_of_dvd_dvd ⟨leadingCoeff r, hr ▸ leadingCoeff_mul p r⟩ h₂
  ⟨Units.map Polynomial.C.toMonoidHom u, Polynomial.eq_of_dvd_of_natDegree_le_of_leadingCoeff
    (by rwa [Units.mul_right_dvd]) (by simpa [natDegree_mul_C] using h₁) (by simpa using hu)⟩

