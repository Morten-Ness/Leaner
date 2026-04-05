import Mathlib

variable {F α β M N P G H : Type*}

variable [EquivLike F α β]

variable [Mul M] [Mul N] [Mul P]

theorem _root_.MulEquivClass.coe_symm_apply_apply {α β} [Mul α] [Mul β] {F} [EquivLike F α β]
    [MulEquivClass F α β] (e : F) (x : α) :
    (e : α ≃* β).symm (e x) = x := (e : α ≃* β).left_inv x

