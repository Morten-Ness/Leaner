import Mathlib

variable {α : Type u} [Mul α]

variable {β : Type v} [Semigroup β] (f : α →ₙ* β)

theorem hom_ext {f g : Magma.AssocQuotient α →ₙ* β} (h : f.comp Magma.AssocQuotient.of = g.comp Magma.AssocQuotient.of) : f = g := (DFunLike.ext _ _) fun x => Magma.AssocQuotient.induction_on x <| DFunLike.congr_fun h

