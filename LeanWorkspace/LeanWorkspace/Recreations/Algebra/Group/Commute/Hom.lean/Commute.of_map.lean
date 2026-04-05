import Mathlib

variable {F M N : Type*} [Mul M] [Mul N] {a x y : M} [FunLike F M N]

theorem Commute.of_map [MulHomClass F M N] {f : F} (hf : Function.Injective f)
    (h : Commute (f x) (f y)) : Commute x y := hf (by simpa only [map_mul] using h.eq)

