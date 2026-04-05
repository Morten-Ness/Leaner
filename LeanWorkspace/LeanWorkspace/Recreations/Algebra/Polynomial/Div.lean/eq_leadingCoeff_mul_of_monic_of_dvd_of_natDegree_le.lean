import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R] {p p₁ p₂ q : R[X]}

variable [IsDomain R]

theorem eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le {R} [CommSemiring R] {p q : R[X]}
    (hp : p.Monic) (hdvd : p ∣ q) (hdeg : q.natDegree ≤ p.natDegree) :
    q = Polynomial.C q.leadingCoeff * p := by
  rw [mul_comm, ← Polynomial.eq_mul_leadingCoeff_of_monic_of_dvd_of_natDegree_le hp hdvd hdeg]

