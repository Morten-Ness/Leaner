import Mathlib

variable {Q : Type*} [Quandle Q]

theorem conj_swap {G : Type*} [Group G] (x y : Conj G) : x ◃ y = y ↔ y ◃ x = x := by
  grind [eq_mul_inv_iff_mul_eq]

