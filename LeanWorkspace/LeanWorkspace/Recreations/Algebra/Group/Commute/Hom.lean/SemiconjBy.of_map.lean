import Mathlib

variable {F M N : Type*} [Mul M] [Mul N] {a x y : M} [FunLike F M N]

theorem SemiconjBy.of_map [MulHomClass F M N] {f : F} (hf : Function.Injective f)
    (h : SemiconjBy (f a) (f x) (f y)) : SemiconjBy a x y := hf (by simpa only [SemiconjBy, map_mul] using h)

