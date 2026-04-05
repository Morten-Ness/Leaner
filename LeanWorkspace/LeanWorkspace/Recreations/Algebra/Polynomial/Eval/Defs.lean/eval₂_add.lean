import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

variable (f : R →+* S) (x : S)

theorem eval₂_add : (p + q).eval₂ f x = p.eval₂ f x + q.eval₂ f x := by
  simp only [Polynomial.eval₂_eq_sum]
  apply sum_add_index <;> simp [add_mul]

