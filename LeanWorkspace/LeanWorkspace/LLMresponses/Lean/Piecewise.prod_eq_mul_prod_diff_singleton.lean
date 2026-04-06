FAIL
import Mathlib

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem prod_eq_mul_prod_diff_singleton [DecidableEq ι] {s : Finset ι} (i : ι) (f : ι → M)
    (h : i ∉ s → f i = 1) : ∏ x ∈ s, f x = f i * ∏ x ∈ s \ {i}, f x := by
  by_cases hi : i ∈ s
  · simpa [Finset.sdiff_singleton_eq_erase, hi, mul_comm] using
      (Finset.prod_erase_mul _ _ hi).symm
  · rw [h hi]
    have hs : s \ {i} = s := by
      ext x
      by_cases hx : x = i
      · subst hx
        simp [hi]
      · simp [hx]
    simp [hs]
