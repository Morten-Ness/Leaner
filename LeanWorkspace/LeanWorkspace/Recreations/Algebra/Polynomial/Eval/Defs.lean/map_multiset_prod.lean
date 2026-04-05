import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [CommSemiring R] [CommSemiring S] (f : R →+* S)

theorem map_multiset_prod (m : Multiset R[X]) : m.prod.map f = (m.map <| Polynomial.map f).prod := Eq.symm <| Multiset.prod_hom _ (Polynomial.mapRingHom f).toMonoidHom

