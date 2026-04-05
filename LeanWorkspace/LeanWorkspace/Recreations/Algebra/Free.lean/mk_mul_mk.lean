import Mathlib

variable {α : Type u}

theorem mk_mul_mk (x y : α) (L1 L2 : List α) : FreeSemigroup.mk x L1 * FreeSemigroup.mk y L2 = FreeSemigroup.mk x (L1 ++ y :: L2) := rfl

