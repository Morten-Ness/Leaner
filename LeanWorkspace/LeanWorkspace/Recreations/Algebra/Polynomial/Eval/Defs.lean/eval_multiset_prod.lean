import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [CommSemiring R] {p q : R[X]} {x : R} [CommSemiring S] (f : R →+* S)

theorem eval_multiset_prod (s : Multiset R[X]) (x : R) : Polynomial.eval x s.prod = (s.map (Polynomial.eval x)).prod := (Polynomial.evalRingHom x).map_multiset_prod s

