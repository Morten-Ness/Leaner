import Mathlib

open scoped Polynomial

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

theorem rename_polynomial_aeval_X {σ τ : Type*} (f : σ → τ) (i : σ) (p : R[X]) :
    rename f (Polynomial.aeval (Polynomial.X i) p) = Polynomial.aeval (Polynomial.X (f i) : MvPolynomial τ R) p := by
  rw [← aeval_algHom_apply, rename_X]

