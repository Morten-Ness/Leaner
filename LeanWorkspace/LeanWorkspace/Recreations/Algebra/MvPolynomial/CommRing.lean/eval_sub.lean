import Mathlib

variable {R : Type u} {S : Type v}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommRing R]

variable {p q : MvPolynomial σ R}

variable [CommRing S]

variable (f : R →+* S) (g : σ → S)

theorem eval_sub (f : σ → R) : eval f (p - q) = eval f p - eval f q := MvPolynomial.eval₂_sub _ _ _

