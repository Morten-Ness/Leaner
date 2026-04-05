import Mathlib

variable {M N γ : Type*}

variable [AddCommMonoid N] [DistribSMul M N] {r : M}

theorem Multiset.smul_sum {s : Multiset N} : r • s.sum = (s.map (r • ·)).sum := (DistribSMul.toAddMonoidHom N r).map_multiset_sum s

