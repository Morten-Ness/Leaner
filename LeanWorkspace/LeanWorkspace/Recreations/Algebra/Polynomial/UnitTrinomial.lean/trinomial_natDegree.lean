import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] (k m n : ℕ) (u v w : R)

theorem trinomial_natDegree (hkm : k < m) (hmn : m < n) (hw : w ≠ 0) :
    (Polynomial.trinomial k m n u v w).natDegree = n := by
  refine
    natDegree_eq_of_degree_eq_some
      ((Finset.sup_le fun i h => ?_).antisymm <|
        le_degree_of_ne_zero <| by rwa [Polynomial.trinomial_leading_coeff' hkm hmn])
  replace h := support_trinomial' k m n u v w h
  rw [mem_insert, mem_insert, mem_singleton] at h
  rcases h with (rfl | rfl | rfl)
  · exact WithBot.coe_le_coe.mpr (hkm.trans hmn).le
  · exact WithBot.coe_le_coe.mpr hmn.le
  · exact le_rfl

