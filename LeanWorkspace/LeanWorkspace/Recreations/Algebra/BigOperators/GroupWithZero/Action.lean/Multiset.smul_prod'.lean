import Mathlib

variable {M N γ : Type*}

variable [Monoid M] [CommMonoid N] [MulDistribMulAction M N]

theorem Multiset.smul_prod' {r : M} {s : Multiset N} : r • s.prod = (s.map (r • ·)).prod := (MulDistribMulAction.toMonoidHom N r).map_multiset_prod s

