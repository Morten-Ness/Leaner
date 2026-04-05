import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable (f : R →+* S₁)

theorem mapAlgHom_coe_ringHom [CommSemiring S₂] [Algebra R S₁] [Algebra R S₂] (f : S₁ →ₐ[R] S₂) :
    ↑(MvPolynomial.mapAlgHom f : _ →ₐ[R] MvPolynomial σ S₂) =
      (MvPolynomial.map ↑f : MvPolynomial σ S₁ →+* MvPolynomial σ S₂) := RingHom.mk_coe _ _ _ _ _

