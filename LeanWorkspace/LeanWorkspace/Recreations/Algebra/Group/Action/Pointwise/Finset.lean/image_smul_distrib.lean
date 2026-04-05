import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

theorem image_smul_distrib [DecidableEq α] [DecidableEq β] [Mul α] [Mul β] [FunLike F α β]
    [MulHomClass F α β] (f : F) (a : α) (s : Finset α) : (a • s).image f = f a • s.image f := image_comm <| map_mul _ _

