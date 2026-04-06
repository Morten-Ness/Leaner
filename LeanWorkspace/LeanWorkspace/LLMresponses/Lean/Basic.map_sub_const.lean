FAIL
import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_sub_const [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b]
    (f : F) (x : G) : f (x - a) = f x - b := by
  simpa [sub_eq_add_neg] using AddConstMapClass.map_const_add (F := F) (G := G) (H := H) (a := a) (b := b) f (-a) x
