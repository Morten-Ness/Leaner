import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable (f : R →+* S₁)

theorem map_map [CommSemiring S₂] (g : S₁ →+* S₂) (p : MvPolynomial σ R) :
    MvPolynomial.map g (MvPolynomial.map f p) = MvPolynomial.map (g.comp f) p := (MvPolynomial.eval₂_comp_left (MvPolynomial.map g) (C.comp f) X p).trans <| by
    congr
    · ext1 a
      simp only [MvPolynomial.map_C, comp_apply, RingHom.coe_comp]
    · ext1 n
      simp only [MvPolynomial.map_X, comp_apply]

