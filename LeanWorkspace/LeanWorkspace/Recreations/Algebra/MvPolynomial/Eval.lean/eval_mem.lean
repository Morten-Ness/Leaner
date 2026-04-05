import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable {S subS : Type*} [CommSemiring S] [SetLike subS S] [SubsemiringClass subS S]

theorem eval_mem {p : MvPolynomial σ S} {s : subS} (hs : ∀ i ∈ p.support, p.coeff i ∈ s) {v : σ → S}
    (hv : ∀ i, v i ∈ s) : MvPolynomial.eval v p ∈ s := MvPolynomial.eval₂_mem hs hv

