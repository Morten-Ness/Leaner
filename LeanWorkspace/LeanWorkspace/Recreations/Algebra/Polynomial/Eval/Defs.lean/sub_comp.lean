import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Ring R] {p q r : R[X]}

theorem sub_comp : (p - q).comp r = p.comp r - q.comp r := Polynomial.eval₂_sub _

