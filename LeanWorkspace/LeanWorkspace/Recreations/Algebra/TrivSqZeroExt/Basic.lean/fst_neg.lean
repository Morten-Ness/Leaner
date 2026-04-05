import Mathlib

open scoped RightActions

variable {T : Type*} {S : Type*} {R : Type u} {M : Type v}

theorem fst_neg [Neg R] [Neg M] (x : tsze R M) : (-x).fst = -x.fst := rfl

