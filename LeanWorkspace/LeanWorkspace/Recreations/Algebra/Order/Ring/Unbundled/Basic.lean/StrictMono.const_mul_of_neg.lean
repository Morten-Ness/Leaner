import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [PartialOrder R] {a b c d : R}

variable [Preorder α] {f : α → R}

theorem StrictMono.const_mul_of_neg [ExistsAddOfLE R] [PosMulStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (hf : StrictMono f) (ha : a < 0) : StrictAnti fun x => a * f x := (strictAnti_mul_left ha).comp_strictMono hf

