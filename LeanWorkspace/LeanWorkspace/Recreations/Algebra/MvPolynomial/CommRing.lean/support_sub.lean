import Mathlib

variable {R : Type u} {S : Type v}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommRing R]

variable {p q : MvPolynomial σ R}

theorem support_sub [DecidableEq σ] (p q : MvPolynomial σ R) :
    (p - q).support ⊆ p.support ∪ q.support := Finsupp.support_sub

