import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

variable (f : R →+* S)

theorem map_list_prod (L : List R[X]) : L.prod.map f = (L.map <| Polynomial.map f).prod := Eq.symm <| List.prod_hom _ (Polynomial.mapRingHom f).toMonoidHom

