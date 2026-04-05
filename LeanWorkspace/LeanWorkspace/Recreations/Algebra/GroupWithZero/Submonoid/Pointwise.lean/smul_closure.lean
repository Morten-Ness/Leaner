import Mathlib

open scoped Pointwise

variable {G₀ G M A : Type*} [Monoid M] [AddMonoid A]

variable [DistribMulAction M A]

theorem smul_closure (m : M) (s : Set A) : m • closure s = closure (m • s) := AddMonoidHom.map_mclosure _ _

