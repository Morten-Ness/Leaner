import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem comp_X : p.comp Polynomial.X = p := by
  simp only [Polynomial.comp, eval₂_def, C_mul_X_pow_eq_monomial]
  exact sum_monomial_eq _

