import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem comp_eq_sum_left : p.comp q = p.sum fun e a => Polynomial.C a * q ^ e := by rw [Polynomial.comp, Polynomial.eval₂_eq_sum]

