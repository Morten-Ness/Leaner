import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem algHom_ext' {A B : Type*} [CommSemiring A] [CommSemiring B] [Algebra R A] [Algebra R B]
    {f g : MvPolynomial σ A →ₐ[R] B}
    (h₁ :
      f.comp (IsScalarTower.toAlgHom R A (MvPolynomial σ A)) =
        g.comp (IsScalarTower.toAlgHom R A (MvPolynomial σ A)))
    (h₂ : ∀ i, f (MvPolynomial.X i) = g (MvPolynomial.X i)) : f = g := AlgHom.coe_ringHom_injective (MvPolynomial.ringHom_ext' (congr_arg AlgHom.toRingHom h₁) h₂)

