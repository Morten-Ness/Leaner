import Mathlib

variable {R : Type u} {S : Type v}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommRing R]

variable {p q : MvPolynomial σ R}

theorem totalDegree_sub_C_le (p : MvPolynomial σ R) (r : R) :
    totalDegree (p - C r) ≤ totalDegree p := (MvPolynomial.totalDegree_sub _ _).trans_eq <| by rw [totalDegree_C, Nat.max_zero]

