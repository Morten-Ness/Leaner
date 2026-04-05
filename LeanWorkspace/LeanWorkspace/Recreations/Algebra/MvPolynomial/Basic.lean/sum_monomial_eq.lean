import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem sum_monomial_eq {A : Type*} [AddCommMonoid A] {u : σ →₀ ℕ} {r : R} {b : (σ →₀ ℕ) → R → A}
    (w : b u 0 = 0) : sum (MvPolynomial.monomial u r) b = b u r := Finsupp.sum_single_index w

