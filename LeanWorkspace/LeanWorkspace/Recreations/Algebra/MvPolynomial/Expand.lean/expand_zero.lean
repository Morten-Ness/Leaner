import Mathlib

variable {σ τ R S : Type*} [CommSemiring R] [CommSemiring S] (p : ℕ)

theorem expand_zero :
    MvPolynomial.expand 0 (σ := σ) (R := R) = .comp (Algebra.ofId R _) (MvPolynomial.aeval (1 : σ → R)) := by
  ext1 i
  simp

