import Mathlib

open scoped Pointwise

variable (G : Type*) (P : Type*) [AddGroup G] [AddTorsor G P]

theorem pointReflection_eq_subLeft {G : Type*} [AddCommGroup G] (x : G) :
    pointReflection x = Equiv.subLeft (2 • x) := by
  ext; simp [pointReflection, sub_add_eq_add_sub, two_nsmul]

