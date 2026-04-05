import Mathlib

variable {F M N : Type*} [Mul M] [Mul N] {a x y : M} [FunLike F M N]

theorem semiconjBy_map_iff [MulHomClass F M N] {f : F} (hf : Function.Injective f) {x y : M} :
    SemiconjBy (f a) (f x) (f y) ↔ SemiconjBy a x y := ⟨.of_map hf, (.map · f)⟩

