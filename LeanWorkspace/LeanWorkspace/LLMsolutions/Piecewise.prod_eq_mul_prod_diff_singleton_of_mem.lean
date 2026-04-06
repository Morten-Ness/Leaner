FAIL
import Mathlib

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem prod_eq_mul_prod_diff_singleton_of_mem [DecidableEq ι] {s : Finset ι} {i : ι} (h : i ∈ s)
    (f : ι → M) : ∏ x ∈ s, f x = f i * ∏ x ∈ s \ {i}, f x := by
  classical
  simpa [Finset.mem_sdiff, h, and_self, Finset.prod_insert, not_false_eq_true] using
    (Finset.prod_insert (s := s \ {i}) (a := i) (f := f)
      (by
        simp)) .symm
