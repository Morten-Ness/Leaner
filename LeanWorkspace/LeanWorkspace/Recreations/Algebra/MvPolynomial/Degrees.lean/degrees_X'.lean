import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem degrees_X' (n : σ) : MvPolynomial.degrees (X n : MvPolynomial σ R) ≤ {n} := le_trans (MvPolynomial.degrees_monomial _ _) <| le_of_eq <| toMultiset_single _ _

