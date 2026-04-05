import Mathlib

variable {α β : Type*}

variable [Mul α] [Preorder α] [Preorder β] {f g : β → α} {s : Set β}

variable [MulLeftMono α] [MulRightStrictMono α]

theorem cmp_mul_right' {α : Type*} [Mul α] [LinearOrder α]
    [MulRightStrictMono α] (a b c : α) :
    cmp (a * c) (b * c) = cmp a b := (strictMono_id.mul_const' c).cmp_map_eq a b

