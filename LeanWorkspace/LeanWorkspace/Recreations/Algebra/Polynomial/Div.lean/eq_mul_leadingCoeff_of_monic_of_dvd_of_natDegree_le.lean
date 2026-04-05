import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R]

variable {p q : R[X]}

theorem eq_mul_leadingCoeff_of_monic_of_dvd_of_natDegree_le {p q : R[X]}
    (hp : p.Monic) (hdvd : p ∣ q) (hdeg : q.natDegree ≤ p.natDegree) :
    q = p * Polynomial.C q.leadingCoeff := by
  obtain ⟨r, rfl⟩ := hdvd
  obtain rfl | hr := eq_or_ne r 0
  · simp
  have : r.natDegree = 0 := by simpa [hp.natDegree_mul' hr] using hdeg
  rw [eq_C_of_natDegree_eq_zero this]
  simp [leadingCoeff_monic_mul hp]

