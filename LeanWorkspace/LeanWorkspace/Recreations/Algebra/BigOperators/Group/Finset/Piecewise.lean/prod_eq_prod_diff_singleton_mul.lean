import Mathlib

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem prod_eq_prod_diff_singleton_mul [DecidableEq ι] {s : Finset ι} {i : ι} (h : i ∈ s)
    (f : ι → M) : ∏ x ∈ s, f x = (∏ x ∈ s \ {i}, f x) * f i := by
  rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem h, mul_comm]

