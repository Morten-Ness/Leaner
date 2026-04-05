import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem totalDegree_monomial (s : σ →₀ ℕ) {c : R} (hc : c ≠ 0) :
    (monomial s c : MvPolynomial σ R).totalDegree = s.sum fun _ e => e := by
  classical simp [MvPolynomial.totalDegree, support_monomial, if_neg hc]

