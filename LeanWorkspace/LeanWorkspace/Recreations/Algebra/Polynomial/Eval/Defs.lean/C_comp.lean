import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem C_comp : (Polynomial.C a).comp p = Polynomial.C a := Polynomial.eval₂_C _ _

