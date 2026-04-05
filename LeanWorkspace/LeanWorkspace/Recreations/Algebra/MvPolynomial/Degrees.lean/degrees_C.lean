import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem degrees_C (a : R) : MvPolynomial.degrees (C a : MvPolynomial σ R) = 0 := Multiset.le_zero.1 <| MvPolynomial.degrees_monomial _ _

