import Mathlib

variable {R : Type u} {S : Type v}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommRing R]

variable {p q : MvPolynomial σ R}

variable [CommRing S]

variable (f : R →+* S) (g : σ → S)

theorem eval₂_neg : (-p).eval₂ f g = -p.eval₂ f g := (eval₂Hom f g).map_neg _

