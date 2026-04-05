import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable {R S σ : Type*} [CommSemiring R] [CommSemiring S]

variable [Algebra R S] {M : Submodule R S}

theorem le_coeffsIn_pow : ∀ {n}, MvPolynomial.coeffsIn σ M ^ n ≤ MvPolynomial.coeffsIn σ (M ^ n)
  | 0 => by simpa using ⟨1, map_one _⟩
  | n + 1 => (MvPolynomial.coeffsIn_pow n.succ_ne_zero _).ge
