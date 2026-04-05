import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem coeff_mul_monomial (m) (s : σ →₀ ℕ) (r : R) (p : MvPolynomial σ R) :
    MvPolynomial.coeff (m + s) (p * MvPolynomial.monomial s r) = MvPolynomial.coeff m p * r := AddMonoidAlgebra.mul_single_apply_aux fun _a _ => add_left_inj _

