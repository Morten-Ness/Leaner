import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_zsmul_add [AddCommGroup G] [AddGroup H] [AddConstMapClass F G H a b]
    (f : F) (n : ℤ) (x : G) : f (n • a + x) = f x + n • b := by
  simpa [add_comm] using AddConstMapClass.map_zsmul_add (f := f) (a := a) (b := b) (n := n) (x := x)
