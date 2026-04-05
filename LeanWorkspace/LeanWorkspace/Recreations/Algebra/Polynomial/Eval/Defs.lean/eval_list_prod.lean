import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [CommSemiring R] {p q : R[X]} {x : R} [CommSemiring S] (f : R →+* S)

theorem eval_list_prod (l : List R[X]) (x : R) : Polynomial.eval x l.prod = (l.map (Polynomial.eval x)).prod := Polynomial.map_list_prod (Polynomial.evalRingHom x) l

