import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

variable (f : R →+* S) (x : S)

variable [Semiring T]

theorem eval₂_list_sum (l : List R[X]) (x : S) : eval₂ f x l.sum = (l.map (eval₂ f x)).sum := map_list_sum (Polynomial.eval₂AddMonoidHom f x) l

