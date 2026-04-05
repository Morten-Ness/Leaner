import Mathlib

variable {F α β M N P G H : Type*}

variable [EquivLike F α β]

variable [Mul M] [Mul N] [Mul P]

theorem _root_.MulEquivClass.apply_coe_symm_apply {α β} [Mul α] [Mul β] {F} [EquivLike F α β]
    [MulEquivClass F α β] (e : F) (x : β) :
    e ((e : α ≃* β).symm x) = x := (e : α ≃* β).right_inv x

