import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [CommSemiring S] (f : R →+* S) (x : S)

theorem eval₂_list_prod (l : List R[X]) (x : S) : eval₂ f x l.prod = (l.map (eval₂ f x)).prod := map_list_prod (Polynomial.eval₂RingHom f x) l

