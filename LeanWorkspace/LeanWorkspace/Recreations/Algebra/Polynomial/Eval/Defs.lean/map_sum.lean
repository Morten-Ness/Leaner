import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

variable (f : R →+* S)

theorem map_sum {ι : Type*} (g : ι → R[X]) (s : Finset ι) :
    (∑ i ∈ s, g i).map f = ∑ i ∈ s, (g i).map f := map_sum (Polynomial.mapRingHom f) _ _

