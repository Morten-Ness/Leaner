import Mathlib

open scoped Pointwise

variable {G₀ G M A : Type*} [Monoid M] [AddMonoid A]

variable [DistribMulAction M A]

theorem smul_sup (m : M) (S T : AddSubmonoid A) : m • (S ⊔ T) = m • S ⊔ m • T := map_sup _ _ _

