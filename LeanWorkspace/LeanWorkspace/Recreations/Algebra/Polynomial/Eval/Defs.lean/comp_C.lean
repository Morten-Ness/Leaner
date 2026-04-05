import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem comp_C : p.comp (Polynomial.C a) = Polynomial.C (p.eval a) := by simp [Polynomial.comp]

