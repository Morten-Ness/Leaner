import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [CommSemiring R] {p q : R[X]} {x : R} [CommSemiring S] (f : R →+* S)

theorem eval₂_multiset_prod (s : Multiset R[X]) (x : S) :
    eval₂ f x s.prod = (s.map (eval₂ f x)).prod := map_multiset_prod (Polynomial.eval₂RingHom f x) s

