import Mathlib

open scoped Pointwise

variable (G : Type*) (P : Type*) [AddGroup G] [AddTorsor G P]

theorem injective_pointReflection_left_of_injective_two_nsmul {G P : Type*} [AddCommGroup G]
    [AddTorsor G P] (h : Function.Injective (2 • · : G → G)) (y : P) :
    Function.Injective fun x : P => pointReflection x y := fun x₁ x₂ (hy : pointReflection x₁ y = pointReflection x₂ y) => by
  rwa [pointReflection_apply, pointReflection_apply, vadd_eq_vadd_iff_sub_eq_vsub,
    vsub_sub_vsub_cancel_right, ← neg_vsub_eq_vsub_rev, neg_eq_iff_add_eq_zero,
    ← two_nsmul, ← nsmul_zero 2, h.eq_iff, vsub_eq_zero_iff_eq] at hy

