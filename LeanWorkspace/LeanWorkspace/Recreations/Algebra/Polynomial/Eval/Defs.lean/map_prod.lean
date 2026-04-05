import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [CommSemiring R] [CommSemiring S] (f : R →+* S)

theorem map_prod {ι : Type*} (g : ι → R[X]) (s : Finset ι) :
    (∏ i ∈ s, g i).map f = ∏ i ∈ s, (g i).map f := map_prod (Polynomial.mapRingHom f) _ _

