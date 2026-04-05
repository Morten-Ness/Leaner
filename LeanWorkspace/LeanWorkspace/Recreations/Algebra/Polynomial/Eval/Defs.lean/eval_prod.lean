import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [CommSemiring R] {p q : R[X]} {x : R} [CommSemiring S] (f : R →+* S)

theorem eval_prod {ι : Type*} (s : Finset ι) (p : ι → R[X]) (x : R) :
    Polynomial.eval x (∏ j ∈ s, p j) = ∏ j ∈ s, Polynomial.eval x (p j) := map_prod (Polynomial.evalRingHom x) _ _

