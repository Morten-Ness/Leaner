import Mathlib

variable {R : Type u} {σ : Type v} {a a' a₁ a₂ : R} {s : σ →₀ ℕ}

variable [CommSemiring R]

theorem pderiv_monomial_single {i : σ} {n : ℕ} : MvPolynomial.pderiv i (monomial (single i n) a) =
    monomial (single i (n - 1)) (a * n) := by simp

