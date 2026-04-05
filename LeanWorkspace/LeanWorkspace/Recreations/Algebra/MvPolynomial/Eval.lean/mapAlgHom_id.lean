import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable (f : R →+* S₁)

theorem mapAlgHom_id [Algebra R S₁] :
    MvPolynomial.mapAlgHom (AlgHom.id R S₁) = AlgHom.id R (MvPolynomial σ S₁) := AlgHom.ext MvPolynomial.map_id

