import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable {R S σ : Type*} [CommSemiring R] [CommSemiring S]

variable [Algebra R S] {M : Submodule R S}

theorem coeffsIn_pow : ∀ {n}, n ≠ 0 → ∀ M : Submodule R S, MvPolynomial.coeffsIn σ (M ^ n) = MvPolynomial.coeffsIn σ M ^ n
  | 1, _, M => by simp
  | n + 2, _, M => by rw [pow_succ, MvPolynomial.coeffsIn_mul, coeffsIn_pow, ← pow_succ]; exact n.succ_ne_zero
