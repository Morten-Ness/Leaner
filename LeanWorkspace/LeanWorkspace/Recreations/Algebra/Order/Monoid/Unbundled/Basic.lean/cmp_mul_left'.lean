import Mathlib

variable {α β : Type*}

variable [Mul α] [Preorder α] [Preorder β] {f g : β → α} {s : Set β}

variable [MulLeftMono α] [MulRightStrictMono α]

theorem cmp_mul_left' {α : Type*} [Mul α] [LinearOrder α] [MulLeftStrictMono α]
    (a b c : α) :
    cmp (a * b) (a * c) = cmp b c := (strictMono_id.const_mul' a).cmp_map_eq b c

