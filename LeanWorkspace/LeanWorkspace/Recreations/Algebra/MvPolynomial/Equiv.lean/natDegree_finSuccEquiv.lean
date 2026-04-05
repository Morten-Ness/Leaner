import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

variable (n : ℕ)

theorem natDegree_finSuccEquiv (f : MvPolynomial (Fin (n + 1)) R) :
    (MvPolynomial.finSuccEquiv R n f).natDegree = degreeOf 0 f := by
  by_cases c : f = 0
  · rw [c, map_zero, Polynomial.natDegree_zero, degreeOf_zero]
  · rw [Polynomial.natDegree, MvPolynomial.degree_finSuccEquiv c, Nat.cast_withBot, WithBot.unbotD_coe]

