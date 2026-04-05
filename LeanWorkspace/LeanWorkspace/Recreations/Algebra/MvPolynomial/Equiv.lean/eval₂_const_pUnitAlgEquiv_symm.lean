import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

theorem eval₂_const_pUnitAlgEquiv_symm {f : Polynomial R} {φ : R →+* S} {a : S} :
    ((MvPolynomial.pUnitAlgEquiv R).symm f : MvPolynomial Unit R).eval₂ φ (fun _ ↦ a) =
      f.eval₂ φ a := by
  rw [MvPolynomial.eval₂_pUnitAlgEquiv_symm]

