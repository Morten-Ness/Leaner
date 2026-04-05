import Mathlib

variable {α : Type u}

theorem hom_ext {β : Type v} [Mul β] {f g : FreeMagma α →ₙ* β} (h : f ∘ of = g ∘ of) : f = g := (DFunLike.ext _ _) fun x ↦ FreeMagma.recOnMul x (congr_fun h) <| by intros; simp only [map_mul, *]

