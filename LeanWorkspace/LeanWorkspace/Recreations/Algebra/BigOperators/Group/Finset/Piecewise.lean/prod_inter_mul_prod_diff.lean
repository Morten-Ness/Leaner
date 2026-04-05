import Mathlib

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem prod_inter_mul_prod_diff [DecidableEq ι] (s t : Finset ι) (f : ι → M) :
    (∏ x ∈ s ∩ t, f x) * ∏ x ∈ s \ t, f x = ∏ x ∈ s, f x := by
  convert (Finset.prod_piecewise s t f f).symm
  simp +unfoldPartialApp [Finset.piecewise]

