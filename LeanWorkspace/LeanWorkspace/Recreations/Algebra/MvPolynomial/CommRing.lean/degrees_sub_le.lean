import Mathlib

variable {R : Type u} {S : Type v}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommRing R]

variable {p q : MvPolynomial σ R}

theorem degrees_sub_le [DecidableEq σ] {p q : MvPolynomial σ R} :
    (p - q).degrees ≤ p.degrees ∪ q.degrees := by
  simpa [degrees_def] using AddMonoidAlgebra.supDegree_sub_le

