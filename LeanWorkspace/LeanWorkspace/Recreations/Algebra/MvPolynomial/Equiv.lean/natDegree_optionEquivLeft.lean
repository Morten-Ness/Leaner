import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

theorem natDegree_optionEquivLeft (p : MvPolynomial (Option σ) R) :
    Polynomial.natDegree (MvPolynomial.optionEquivLeft R σ p) = p.degreeOf none := by
  by_cases c : p = 0
  · rw [c, map_zero, Polynomial.natDegree_zero, degreeOf_zero]
  · rw [Polynomial.natDegree, MvPolynomial.degree_optionEquivLeft R c, Nat.cast_withBot, WithBot.unbotD_coe]

