import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem degrees_one : MvPolynomial.degrees (1 : MvPolynomial σ R) = 0 := MvPolynomial.degrees_C 1

