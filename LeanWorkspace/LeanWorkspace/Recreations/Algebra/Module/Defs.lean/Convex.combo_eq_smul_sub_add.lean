import Mathlib

variable {R S M M₂ : Type*}

variable [Semiring R] [AddCommGroup M]

theorem Convex.combo_eq_smul_sub_add [Module R M] {x y : M} {a b : R} (h : a + b = 1) :
    a • x + b • y = b • (y - x) + x := calc
    a • x + b • y = b • y - b • x + (a • x + b • x) := by rw [sub_add_add_cancel, add_comm]
    _ = b • (y - x) + x := by rw [smul_sub, Convex.combo_self h]

