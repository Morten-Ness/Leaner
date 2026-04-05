import Mathlib

open scoped Pointwise

variable {G₀ G M A : Type*} [Monoid M] [AddMonoid A]

variable [DistribMulAction M A]

theorem smul_bot (m : M) : m • (⊥ : AddSubmonoid A) = ⊥ := map_bot _

