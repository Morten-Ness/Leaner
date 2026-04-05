import Mathlib

open scoped Pointwise

variable (G : Type*) (P : Type*) [AddGroup G] [AddTorsor G P]

theorem pointReflection_fixed_iff_of_injective_two_nsmul {x y : P} (h : Function.Injective (2 • · : G → G)) :
    pointReflection x y = y ↔ y = x := by
  rw [pointReflection_apply, eq_comm, eq_vadd_iff_vsub_eq, ← neg_vsub_eq_vsub_rev,
    neg_eq_iff_add_eq_zero, ← two_nsmul, ← nsmul_zero 2, h.eq_iff, vsub_eq_zero_iff_eq, eq_comm]

