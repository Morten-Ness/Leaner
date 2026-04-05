import Mathlib

variable {F M N : Type*}

variable [Monoid M] [Monoid N] {f : F} {x y : M}

theorem IsSquare.not_irreducible (ha : IsSquare x) : ¬Irreducible x := fun h => h.not_isSquare ha

