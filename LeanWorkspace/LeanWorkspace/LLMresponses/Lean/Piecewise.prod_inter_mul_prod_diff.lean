FAIL
import Mathlib

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem prod_inter_mul_prod_diff [DecidableEq ι] (s t : Finset ι) (f : ι → M) :
    (∏ x ∈ s ∩ t, f x) * ∏ x ∈ s \ t, f x = ∏ x ∈ s, f x := by
  classical
  simpa [Finset.prod_filter, Finset.filter_mem_eq_inter, Finset.filter_true, Finset.mem_sdiff] using
    (Finset.prod_filter_mul_prod_filter_not (s := s) (p := fun x => x ∈ t) (f := f)).symm
