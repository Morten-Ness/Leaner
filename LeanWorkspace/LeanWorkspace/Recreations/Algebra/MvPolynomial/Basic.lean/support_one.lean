import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem support_one [Nontrivial R] : (1 : MvPolynomial σ R).support = {0} := by
  classical
  simp [show MvPolynomial.support (1 : MvPolynomial σ R) = if (1 : R) = 0 then ∅ else {0} from rfl]

