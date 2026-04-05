import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

variable (f : R →+* S) (x : S)

variable [Semiring T]

theorem eval₂_mul_X : eval₂ f x (p * Polynomial.X) = eval₂ f x p * x := by
  refine _root_.trans (Polynomial.eval₂_mul_noncomm _ _ fun k => ?_) (by rw [Polynomial.eval₂_X])
  rcases em (k = 1) with (rfl | hk)
  · simp
  · simp [coeff_X_of_ne_one hk]

