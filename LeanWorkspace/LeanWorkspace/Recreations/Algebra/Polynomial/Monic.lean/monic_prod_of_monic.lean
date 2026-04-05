import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [CommSemiring R] {p : R[X]}

theorem monic_prod_of_monic (s : Finset ι) (f : ι → R[X]) (hs : ∀ i ∈ s, Polynomial.Monic (f i)) :
    Polynomial.Monic (∏ i ∈ s, f i) := Polynomial.monic_multiset_prod_of_monic s.1 f hs

