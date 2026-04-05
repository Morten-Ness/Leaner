import Mathlib

variable {M N γ : Type*}

variable [Monoid M] [Monoid N] [MulDistribMulAction M N]

theorem List.smul_prod' {r : M} {l : List N} : r • l.prod = (l.map (r • ·)).prod := map_list_prod (MulDistribMulAction.toMonoidHom N r) l

