FAIL
import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_sub_int' [AddGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) (n : ℤ) : f (x - n) = f x - n • b := by
  simpa [sub_eq_add_neg, zsmul_neg'] using
    (AddConstMapClass.map_int_add (F := F) (G := G) (H := H) (f := f) (x := x) (n := -n))
