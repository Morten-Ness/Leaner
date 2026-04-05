import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

theorem image_smul_distrib [Mul α] [Mul β] [FunLike F α β] [MulHomClass F α β]
    (f : F) (a : α) (s : Set α) :
    f '' (a • s) = f a • f '' s := image_comm <| map_mul _ _

