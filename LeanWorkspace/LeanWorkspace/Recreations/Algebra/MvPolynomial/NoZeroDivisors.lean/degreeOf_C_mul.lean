import Mathlib

variable {R : Type*}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R]

variable {p q : MvPolynomial σ R}

theorem degreeOf_C_mul (j : σ) (c : R) (hc : c ∈ R⁰) : degreeOf j (C c * p) = degreeOf j p := by
  by_cases hp : p = 0
  · simp [hp]
  classical
  simp_rw [degreeOf_eq_natDegree, map_mul, ← renameEquiv_apply]
  rw [Polynomial.natDegree_mul']
  · simp
  · have hp' : (optionEquivLeft R _ ((rename (optionSubtypeNe j).symm) p)).leadingCoeff ≠ 0 := by
      intro h
      exact hp (rename_injective _ (Equiv.injective _) (by simpa using h))
    simp_rw [ne_eq, renameEquiv_apply, algHom_C, algebraMap_eq, optionEquivLeft_C,
      Polynomial.leadingCoeff_C]
    contrapose! hp'
    ext m
    apply hc.1
    simpa using congr_arg (coeff m) hp'

