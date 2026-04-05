import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R] {p p₁ p₂ q : R[X]}

variable [IsDomain R]

theorem associated_of_dvd_of_degree_eq {K} [Field K] {p q : K[X]} (hpq : p ∣ q)
    (h₁ : p.degree = q.degree) : Associated p q := (Classical.em (q = 0)).elim (fun hq ↦ (show p = q by simpa [hq] using h₁) ▸ Associated.refl p)
    (Polynomial.associated_of_dvd_of_natDegree_le hpq · (natDegree_le_natDegree h₁.ge))

