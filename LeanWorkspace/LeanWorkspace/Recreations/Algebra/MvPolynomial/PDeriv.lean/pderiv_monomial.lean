import Mathlib

variable {R : Type u} {σ : Type v} {a a' a₁ a₂ : R} {s : σ →₀ ℕ}

variable [CommSemiring R]

theorem pderiv_monomial {i : σ} :
    MvPolynomial.pderiv i (monomial s a) = monomial (s - single i 1) (a * s i) := by
  classical
  simp only [MvPolynomial.pderiv_def, mkDerivation_monomial, Finsupp.smul_sum, smul_eq_mul, ← smul_mul_assoc,
    ← (monomial _).map_smul]
  refine (Finset.sum_eq_single i (fun j _ hne => ?_) fun hi => ?_).trans ?_
  · simp [Pi.single_eq_of_ne hne]
  · rw [Finsupp.notMem_support_iff] at hi; simp [hi]
  · simp

