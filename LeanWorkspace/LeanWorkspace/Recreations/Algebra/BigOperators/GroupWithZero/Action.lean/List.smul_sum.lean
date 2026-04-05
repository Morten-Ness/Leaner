import Mathlib

variable {M N γ : Type*}

variable [AddMonoid N] [DistribSMul M N]

theorem List.smul_sum {r : M} {l : List N} : r • l.sum = (l.map (r • ·)).sum := map_list_sum (DistribSMul.toAddMonoidHom N r) l

