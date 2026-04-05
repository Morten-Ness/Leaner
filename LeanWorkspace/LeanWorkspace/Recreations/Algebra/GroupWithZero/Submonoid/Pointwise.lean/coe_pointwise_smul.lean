import Mathlib

open scoped Pointwise

variable {G₀ G M A : Type*} [Monoid M] [AddMonoid A]

variable [DistribMulAction M A]

theorem coe_pointwise_smul (m : M) (S : AddSubmonoid A) : ↑(m • S) = m • (S : Set A) := rfl

