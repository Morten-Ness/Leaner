import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

theorem eval₂_const_pUnitAlgEquiv {f : MvPolynomial PUnit R} {φ : R →+* S} {a : S} :
    ((MvPolynomial.pUnitAlgEquiv R) f : Polynomial R).eval₂ φ a = f.eval₂ φ (fun _ ↦ a) := by
  rw [← MvPolynomial.eval₂_pUnitAlgEquiv]

