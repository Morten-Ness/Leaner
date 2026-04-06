FAIL
import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_sub_zsmul [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b]
    (f : F) (x : G) (n : ℤ) : f (x - n • a) = f x - n • b := by
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    (map_zsmul (f := f) (x := x) (n := -n) (a := a) (b := b))
