import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem degrees_add_le [DecidableEq σ] {p q : MvPolynomial σ R} :
    (p + q).degrees ≤ p.degrees ⊔ q.degrees := by
  simp_rw [MvPolynomial.degrees_def]; exact supDegree_add_le

