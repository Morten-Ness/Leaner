import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem comp_one : p.comp 1 = Polynomial.C (p.eval 1) := by rw [← C_1, Polynomial.comp_C]

