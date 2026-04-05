import Mathlib

variable {R : Type*} [Mul R] [StarMul R] {a : R} {s : Set R}

theorem Set.star_centralizer : star s.centralizer = (star s).centralizer := by
  simp_rw [centralizer, ← commute_iff_eq]
  conv_lhs => simp only [← star_preimage, preimage_setOf_eq, ← commute_star_comm]
  conv_rhs => simp only [← image_star, forall_mem_image]

