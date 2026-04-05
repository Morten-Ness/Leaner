import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

variable (f : R →+* S)

theorem map_map [Semiring T] (g : S →+* T) (p : R[X]) : (p.map f).map g = p.map (g.comp f) := ext (by simp [Polynomial.coeff_map])

