import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [CommSemiring R] {p q : R[X]} {x : R} [CommSemiring S] (f : R →+* S)

theorem prod_comp {ι : Type*} (s : Finset ι) (p : ι → R[X]) (q : R[X]) :
    (∏ j ∈ s, p j).comp q = ∏ j ∈ s, (p j).comp q := map_prod (Polynomial.compRingHom q) _ _

