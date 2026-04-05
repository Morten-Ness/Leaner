import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable (f : R →+* S₁)

theorem coeff_map (p : MvPolynomial σ R) : ∀ m : σ →₀ ℕ, coeff m (MvPolynomial.map f p) = f (coeff m p) := by
  classical
  apply MvPolynomial.induction_on p <;> clear p
  · intro r m
    simp_rw [MvPolynomial.map_C, coeff_C, apply_ite f, f.map_zero]
  · intro p q hp hq m
    simp only [hp, hq, (MvPolynomial.map f).map_add, coeff_add, f.map_add]
  · intro p i hp m
    simp only [(MvPolynomial.map f).map_mul, MvPolynomial.map_X, hp, coeff_mul_X', f.map_zero, apply_ite f]

