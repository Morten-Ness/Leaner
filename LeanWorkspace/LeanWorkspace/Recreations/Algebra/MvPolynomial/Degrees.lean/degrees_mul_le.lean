import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem degrees_mul_le {p q : MvPolynomial σ R} : (p * q).degrees ≤ p.degrees + q.degrees := by
  classical
  simp_rw [MvPolynomial.degrees_def]
  exact supDegree_mul_le (map_add _)

