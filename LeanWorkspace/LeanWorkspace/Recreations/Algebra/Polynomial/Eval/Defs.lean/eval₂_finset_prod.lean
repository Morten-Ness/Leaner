import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [CommSemiring R] {p q : R[X]} {x : R} [CommSemiring S] (f : R →+* S)

theorem eval₂_finset_prod (s : Finset ι) (g : ι → R[X]) (x : S) :
    (∏ i ∈ s, g i).eval₂ f x = ∏ i ∈ s, (g i).eval₂ f x := map_prod (Polynomial.eval₂RingHom f x) _ _

