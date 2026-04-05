import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem degrees_X [Nontrivial R] (n : σ) : MvPolynomial.degrees (X n : MvPolynomial σ R) = {n} := (MvPolynomial.degrees_monomial_eq _ (1 : R) one_ne_zero).trans (toMultiset_single _ _)

