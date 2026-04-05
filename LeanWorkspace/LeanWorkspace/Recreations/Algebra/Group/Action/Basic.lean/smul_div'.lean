import Mathlib

variable {G M A B α β : Type*}

variable [Monoid M] [Group A] [MulDistribMulAction M A]

theorem smul_div' (r : M) (x y : A) : r • (x / y) = r • x / r • y := map_div (MulDistribMulAction.toMonoidHom A r) x y

