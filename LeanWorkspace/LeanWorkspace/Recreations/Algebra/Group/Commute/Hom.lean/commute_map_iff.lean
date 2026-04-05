import Mathlib

variable {F M N : Type*} [Mul M] [Mul N] {a x y : M} [FunLike F M N]

theorem commute_map_iff [MulHomClass F M N] {f : F} (hf : Function.Injective f) {x y : M} :
    Commute (f x) (f y) ↔ Commute x y := ⟨.of_map hf, (.map · f)⟩

