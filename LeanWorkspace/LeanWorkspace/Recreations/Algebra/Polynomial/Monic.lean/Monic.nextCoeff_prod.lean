import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [CommSemiring R] {p : R[X]}

theorem Monic.nextCoeff_prod (s : Finset ι) (f : ι → R[X]) (h : ∀ i ∈ s, Polynomial.Monic (f i)) :
    nextCoeff (∏ i ∈ s, f i) = ∑ i ∈ s, nextCoeff (f i) := Polynomial.Monic.nextCoeff_multiset_prod s.1 f h

