import Mathlib

open scoped Function -- required for scoped `on` notation

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

theorem natDegree_map_eq_of_injective {f : R →+* S} (hf : Function.Injective f) (p : Polynomial R) :
    (p.map f).natDegree = p.natDegree := natDegree_eq_of_degree_eq <| Polynomial.degree_map_eq_of_injective hf _

