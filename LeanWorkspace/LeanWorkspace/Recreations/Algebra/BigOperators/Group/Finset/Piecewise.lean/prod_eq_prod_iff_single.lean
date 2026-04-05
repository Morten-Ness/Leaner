import Mathlib

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem prod_eq_prod_iff_single [IsRightCancelMul M] {f g : ι → M} {i : ι} (hi : i ∈ s)
    (hfg : ∀ j ∈ s, j ≠ i → f j = g j) : ∏ j ∈ s, f j = ∏ j ∈ s, g j ↔ f i = g i := by
  classical
  rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem hi, Finset.prod_eq_mul_prod_diff_singleton_of_mem hi,
    prod_congr rfl (by simpa), mul_left_inj]

