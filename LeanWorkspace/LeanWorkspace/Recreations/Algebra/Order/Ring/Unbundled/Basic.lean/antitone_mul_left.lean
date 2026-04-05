import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [Preorder R] {a b c d : R}

variable [Preorder α] {f g : α → R}

theorem antitone_mul_left [ExistsAddOfLE R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    {a : R} (ha : a ≤ 0) : Antitone (a * ·) := fun _ _ b_le_c =>
  mul_le_mul_of_nonpos_left b_le_c ha

