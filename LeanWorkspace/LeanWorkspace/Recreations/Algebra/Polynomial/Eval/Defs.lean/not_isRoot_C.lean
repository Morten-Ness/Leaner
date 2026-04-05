import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable {x : R}

theorem not_isRoot_C (r a : R) (hr : r ≠ 0) : ¬Polynomial.IsRoot (Polynomial.C r) a := by simpa using hr

