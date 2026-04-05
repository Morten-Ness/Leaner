import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

theorem sumToIter_C (a : R) : MvPolynomial.sumToIter R S₁ S₂ (Polynomial.C a) = Polynomial.C (Polynomial.C a) := eval₂_C _ _ a

