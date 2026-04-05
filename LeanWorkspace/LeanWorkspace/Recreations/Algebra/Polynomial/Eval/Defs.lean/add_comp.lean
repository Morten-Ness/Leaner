import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem add_comp : (p + q).comp r = p.comp r + q.comp r := Polynomial.eval₂_add _ _

