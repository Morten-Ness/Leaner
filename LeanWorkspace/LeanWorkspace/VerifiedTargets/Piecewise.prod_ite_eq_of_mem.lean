import Mathlib

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem prod_ite_eq_of_mem [DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M) (h : a ∈ s) :
    (∏ x ∈ s, if a = x then b x else 1) = b a := by
  simp only [Finset.prod_ite_eq, if_pos h]

