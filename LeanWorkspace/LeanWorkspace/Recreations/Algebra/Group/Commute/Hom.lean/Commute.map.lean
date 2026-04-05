import Mathlib

variable {F M N : Type*} [Mul M] [Mul N] {a x y : M} [FunLike F M N]

theorem Commute.map [MulHomClass F M N] (h : Commute x y) (f : F) : Commute (f x) (f y) := SemiconjBy.map h f

