import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem coeff_monomial_mul (m) (s : σ →₀ ℕ) (r : R) (p : MvPolynomial σ R) :
    MvPolynomial.coeff (s + m) (MvPolynomial.monomial s r * p) = r * MvPolynomial.coeff m p := AddMonoidAlgebra.single_mul_apply_aux fun _a _ => add_right_inj _

