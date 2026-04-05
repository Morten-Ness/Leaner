import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable (f : R →+* S₁)

theorem map_mapRange_eq_iff (f : R →+* S₁) (g : S₁ → R) (hg : g 0 = 0) (φ : MvPolynomial σ S₁) :
    MvPolynomial.map f (Finsupp.mapRange g hg φ) = φ ↔ ∀ d, f (g (coeff d φ)) = coeff d φ := by
  simp_rw [MvPolynomial.ext_iff, MvPolynomial.coeff_map, coeff_mapRange]

