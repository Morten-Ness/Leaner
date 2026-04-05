import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [CommSemiring R] {p q : R[X]} {x : R} [CommSemiring S] (f : R →+* S)

theorem list_prod_comp (l : List R[X]) (q : R[X]) :
    l.prod.comp q = (l.map fun p : R[X] => p.comp q).prod := Polynomial.map_list_prod (Polynomial.compRingHom q) _

