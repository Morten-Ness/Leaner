import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem totalDegree_multiset_prod (s : Multiset (MvPolynomial σ R)) :
    s.prod.totalDegree ≤ (s.map MvPolynomial.totalDegree).sum := s.apply_prod_le_sum_map _ MvPolynomial.totalDegree_one.le MvPolynomial.totalDegree_mul

