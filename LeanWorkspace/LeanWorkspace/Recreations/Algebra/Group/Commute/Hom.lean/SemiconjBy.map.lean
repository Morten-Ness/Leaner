import Mathlib

variable {F M N : Type*} [Mul M] [Mul N] {a x y : M} [FunLike F M N]

theorem SemiconjBy.map [MulHomClass F M N] (h : SemiconjBy a x y) (f : F) :
    SemiconjBy (f a) (f x) (f y) := by simpa only [SemiconjBy, map_mul] using congr_arg f h

