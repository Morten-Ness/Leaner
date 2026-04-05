import Mathlib

open scoped Pointwise RightActions

variable {F α β γ : Type*}

theorem image_op_smul_distrib [Mul α] [Mul β] [FunLike F α β] [MulHomClass F α β]
    (f : F) (a : α) (s : Set α) : f '' (s <• a) = f '' s <• f a := image_comm fun _ ↦ map_mul ..

