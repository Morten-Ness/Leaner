import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable {x : R}

theorem IsRoot.def : Polynomial.IsRoot p a ↔ p.eval a = 0 := Iff.rfl

