import Mathlib

variable {α : Type u}

theorem hom_ext {β : Type v} [Mul β] {f g : FreeSemigroup α →ₙ* β} (h : f ∘ FreeSemigroup.of = g ∘ FreeSemigroup.of) : f = g := (DFunLike.ext _ _) fun x ↦
    FreeSemigroup.recOnMul x (congr_fun h) fun x y hx hy ↦ by simp only [map_mul, *]

