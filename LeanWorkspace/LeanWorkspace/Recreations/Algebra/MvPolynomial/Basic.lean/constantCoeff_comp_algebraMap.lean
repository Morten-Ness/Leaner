import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem constantCoeff_comp_algebraMap :
    MvPolynomial.constantCoeff.comp (algebraMap R (MvPolynomial σ R)) = RingHom.id R := MvPolynomial.constantCoeff_comp_C _ _

