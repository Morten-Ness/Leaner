import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] (k m n : ℕ) (u v w : R)

set_option backward.isDefEq.respectTransparency false in
theorem trinomial_natTrailingDegree (hkm : k < m) (hmn : m < n) (hu : u ≠ 0) :
    (Polynomial.trinomial k m n u v w).natTrailingDegree = k := by
  refine
    natTrailingDegree_eq_of_trailingDegree_eq_some
      ((Finset.le_inf fun i h => ?_).antisymm <|
          trailingDegree_le_of_ne_zero <| by rwa [Polynomial.trinomial_trailing_coeff' hkm hmn]).symm
  replace h := support_trinomial' k m n u v w h
  rw [mem_insert, mem_insert, mem_singleton] at h
  rcases h with (rfl | rfl | rfl)
  · exact le_rfl
  · exact WithTop.coe_le_coe.mpr hkm.le
  · exact WithTop.coe_le_coe.mpr (hkm.trans hmn).le

