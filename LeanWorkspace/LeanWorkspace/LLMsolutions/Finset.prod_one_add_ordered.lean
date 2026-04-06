FAIL
import Mathlib

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable [CommSemiring R]

theorem prod_one_add_ordered [LinearOrder ι] (s : Finset ι) (f : ι → R) :
    ∏ i ∈ s, (1 + f i) = 1 + ∑ i ∈ s, f i * ∏ j ∈ s with j < i, (1 + f j) := by
  classical
  rw [Finset.prod_apply_dite]
  simp_rw [Pi.one_apply, one_mul]
  exact Finset.sum_mul_prod_eq_prod_add s (fun i => f i)
