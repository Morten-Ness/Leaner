import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

variable (n : ℕ)

theorem finSuccEquiv_X_succ {j : Fin n} : MvPolynomial.finSuccEquiv R n (Polynomial.X j.succ) = Polynomial.C (Polynomial.X j) := by
  simp [MvPolynomial.finSuccEquiv_apply]

