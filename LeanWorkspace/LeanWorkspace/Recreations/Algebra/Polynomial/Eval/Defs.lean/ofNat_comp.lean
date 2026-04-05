import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem ofNat_comp (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : R[X]).comp p = n := Polynomial.natCast_comp

