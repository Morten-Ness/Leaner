import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable {S A B : Type*} [CommSemiring S] [CommSemiring A] [CommSemiring B]

variable [Algebra S R] [Algebra S A] [Algebra S B]

variable (g : R →ₐ[S] A) (y : σ → A)

theorem aevalTower_ofNat (n : Nat) [n.AtLeastTwo] :
    MvPolynomial.aevalTower g y (ofNat(n) : MvPolynomial σ R) = ofNat(n) := _root_.map_ofNat _ _

