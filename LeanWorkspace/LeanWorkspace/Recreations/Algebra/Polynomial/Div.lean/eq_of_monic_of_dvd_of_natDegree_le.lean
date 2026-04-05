import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R]

variable {p q : R[X]}

theorem eq_of_monic_of_dvd_of_natDegree_le {p q : R[X]} (hp : p.Monic)
    (hq : q.Monic) (hdvd : p ∣ q) (hdeg : q.natDegree ≤ p.natDegree) : q = p := by
  rw [Polynomial.eq_mul_leadingCoeff_of_monic_of_dvd_of_natDegree_le hp hdvd hdeg]
  simp [hq]

