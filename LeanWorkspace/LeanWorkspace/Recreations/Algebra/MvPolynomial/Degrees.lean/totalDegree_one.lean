import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem totalDegree_one : (1 : MvPolynomial σ R).totalDegree = 0 := MvPolynomial.totalDegree_C (1 : R)

