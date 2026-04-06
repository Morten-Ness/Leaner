FAIL
import Mathlib

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem prod_eq_prod_diff_singleton_mul [DecidableEq ι] {s : Finset ι} {i : ι} (h : i ∈ s)
    (f : ι → M) : ∏ x ∈ s, f x = (∏ x ∈ s \ {i}, f x) * f i := by
  classical
  rw [Finset.prod_erase_mul _ _ h]
  simp [Finset.erase_eq_of_mem h, Finset.mul_comm]
