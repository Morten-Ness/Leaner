import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommSemiring R] [Semiring A] [CommSemiring A'] [Semiring B]

variable [Algebra R A] [Algebra R B]

variable {p q : R[X]} (x : A)

theorem aeval_eq_aeval_map [Semiring S] [CommSemiring T] [Algebra R S]
    [Algebra T S] {φ : R →+* T} (h : (algebraMap T S).comp φ = (algebraMap R S))
    (p : R[X]) (a : S) : Polynomial.aeval a p = Polynomial.aeval a (p.map φ) := Polynomial.map_aeval_eq_aeval_map (by rwa [RingHom.id_comp]) p a

