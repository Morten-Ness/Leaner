import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

variable (f : R →+* S) (x : S)

theorem eval₂_X_pow {n : ℕ} : (Polynomial.X ^ n).eval₂ f x = x ^ n := by
  rw [X_pow_eq_monomial]
  convert Polynomial.eval₂_monomial f x (n := n) (r := 1)
  simp

