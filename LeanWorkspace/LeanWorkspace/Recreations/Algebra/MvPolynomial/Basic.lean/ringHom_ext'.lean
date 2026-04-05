import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem ringHom_ext' {A : Type*} [Semiring A] {f g : MvPolynomial σ R →+* A}
    (hC : f.comp MvPolynomial.C = g.comp MvPolynomial.C) (hX : ∀ i, f (MvPolynomial.X i) = g (MvPolynomial.X i)) : f = g := MvPolynomial.ringHom_ext (RingHom.ext_iff.1 hC) hX

