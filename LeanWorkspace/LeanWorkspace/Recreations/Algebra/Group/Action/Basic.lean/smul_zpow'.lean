import Mathlib

variable {G M A B α β : Type*}

variable [Monoid M] [Group A] [MulDistribMulAction M A]

theorem smul_zpow' (r : M) (x : A) (z : ℤ) : r • (x ^ z) = (r • x) ^ z := map_zpow (MulDistribMulAction.toMonoidHom A r) x z

