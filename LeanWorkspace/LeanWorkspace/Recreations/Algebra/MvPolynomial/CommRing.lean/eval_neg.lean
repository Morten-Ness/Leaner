import Mathlib

variable {R : Type u} {S : Type v}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommRing R]

variable {p q : MvPolynomial σ R}

variable [CommRing S]

variable (f : R →+* S) (g : σ → S)

theorem eval_neg (f : σ → R) : eval f (-p) = -eval f p := MvPolynomial.eval₂_neg _ _ _

