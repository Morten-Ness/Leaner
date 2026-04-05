import Mathlib

variable {R : Type u} {ι : Type w}

variable (s : Finset ι)

variable [CommRing R]

theorem prod_X_sub_C_nextCoeff {s : Finset ι} (f : ι → R) :
    nextCoeff (∏ i ∈ s, (Polynomial.X - Polynomial.C (f i))) = -∑ i ∈ s, f i := by
  simpa using Polynomial.multiset_prod_X_sub_C_nextCoeff (s.1.map f)

