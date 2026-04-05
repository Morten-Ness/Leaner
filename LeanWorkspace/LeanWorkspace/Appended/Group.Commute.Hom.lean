import Mathlib

section

variable {F M N : Type*} [Mul M] [Mul N] {a x y : M} [FunLike F M N]

theorem Commute.of_map [MulHomClass F M N] {f : F} (hf : Function.Injective f)
    (h : Commute (f x) (f y)) : Commute x y := hf (by simpa only [map_mul] using h.eq)

end

section

variable {F M N : Type*} [Mul M] [Mul N] {a x y : M} [FunLike F M N]

theorem SemiconjBy.map [MulHomClass F M N] (h : SemiconjBy a x y) (f : F) :
    SemiconjBy (f a) (f x) (f y) := by simpa only [SemiconjBy, map_mul] using congr_arg f h

end

section

variable {F M N : Type*} [Mul M] [Mul N] {a x y : M} [FunLike F M N]

theorem SemiconjBy.of_map [MulHomClass F M N] {f : F} (hf : Function.Injective f)
    (h : SemiconjBy (f a) (f x) (f y)) : SemiconjBy a x y := hf (by simpa only [SemiconjBy, map_mul] using h)

end
