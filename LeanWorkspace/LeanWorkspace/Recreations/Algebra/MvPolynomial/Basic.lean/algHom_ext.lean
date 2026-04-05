import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem algHom_ext {A : Type*} [Semiring A] [Algebra R A] {f g : MvPolynomial σ R →ₐ[R] A}
    (hf : ∀ i : σ, f (MvPolynomial.X i) = g (MvPolynomial.X i)) : f = g := AddMonoidAlgebra.algHom_ext' (mulHom_ext' fun MvPolynomial.X : σ => MonoidHom.ext_mnat (hf MvPolynomial.X))

