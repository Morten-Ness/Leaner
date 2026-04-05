import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

variable (f : R →+* S) (x : S)

theorem eval₂_monomial {n : ℕ} {r : R} : (monomial n r).eval₂ f x = f r * x ^ n := by
  simp [Polynomial.eval₂_eq_sum]

