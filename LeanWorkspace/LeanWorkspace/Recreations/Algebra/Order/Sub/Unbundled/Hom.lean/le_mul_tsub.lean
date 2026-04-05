import Mathlib

variable {α β : Type*}

variable [Preorder α] [Add α] [Sub α] [OrderedSub α]

theorem le_mul_tsub {R : Type*} [Distrib R] [Preorder R] [Sub R] [OrderedSub R]
    [MulLeftMono R] {a b c : R} : a * b - a * c ≤ a * (b - c) := (AddHom.mulLeft a).le_map_tsub (monotone_id.const_mul' a) _ _

