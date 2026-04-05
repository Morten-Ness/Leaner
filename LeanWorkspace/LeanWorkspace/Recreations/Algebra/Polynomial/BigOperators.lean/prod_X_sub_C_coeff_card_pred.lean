import Mathlib

variable {R : Type u} {ι : Type w}

variable (s : Finset ι)

variable [CommRing R]

theorem prod_X_sub_C_coeff_card_pred (s : Finset ι) (f : ι → R) (hs : 0 < #s) :
    (∏ i ∈ s, (Polynomial.X - Polynomial.C (f i))).coeff (#s - 1) = -∑ i ∈ s, f i := by
  simpa using Polynomial.multiset_prod_X_sub_C_coeff_card_pred (s.1.map f) (by simpa using hs)

