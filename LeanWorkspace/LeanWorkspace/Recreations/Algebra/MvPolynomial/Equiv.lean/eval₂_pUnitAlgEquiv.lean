import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

theorem eval₂_pUnitAlgEquiv {f : MvPolynomial PUnit R} {φ : R →+* S} {a : PUnit → S} :
    ((MvPolynomial.pUnitAlgEquiv R) f : Polynomial R).eval₂ φ (a default) = f.eval₂ φ a := by
  simp only [MvPolynomial.pUnitAlgEquiv_apply]
  induction f using MvPolynomial.induction_on' with
  | monomial d r => simp
  | add f g hf hg => simp [hf, hg]

