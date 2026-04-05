import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

theorem eval₂_pUnitAlgEquiv_symm {f : Polynomial R} {φ : R →+* S} {a : Unit → S} :
    ((MvPolynomial.pUnitAlgEquiv R).symm f : MvPolynomial Unit R).eval₂ φ a =
      f.eval₂ φ (a ()) := by
  simp only [MvPolynomial.pUnitAlgEquiv_symm_apply]
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp [hf, hg]
  | monomial n r => simp

