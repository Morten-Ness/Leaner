import Mathlib

variable {σ R : Type*} [CommSemiring R]

variable {R : Type*} [CommRing R] {i : σ} {p q r : MvPolynomial σ R}

theorem X_prime [IsCancelMulZero R] [Nontrivial R] : Prime (X i : MvPolynomial σ R) := by
  refine ⟨X_ne_zero i, ?_, fun p q ↦ MvPolynomial.X_dvd_mul_iff.mp⟩
  intro h
  rw [isUnit_iff_exists] at h
  rcases h with ⟨u, hu, -⟩
  apply_fun constantCoeff at hu
  simp at hu

