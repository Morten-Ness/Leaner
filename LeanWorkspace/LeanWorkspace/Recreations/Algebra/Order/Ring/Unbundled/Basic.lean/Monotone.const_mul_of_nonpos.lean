import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [Preorder R] {a b c d : R}

variable [Preorder α] {f g : α → R}

theorem Monotone.const_mul_of_nonpos [ExistsAddOfLE R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hf : Monotone f) (ha : a ≤ 0) : Antitone fun x => a * f x := (antitone_mul_left ha).comp_monotone hf

