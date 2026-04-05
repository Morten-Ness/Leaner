import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem totalDegree_C (a : R) : (C a : MvPolynomial σ R).totalDegree = 0 := (supDegree_single 0 a).trans <| by rw [sum_zero_index, bot_eq_zero', ite_self]

