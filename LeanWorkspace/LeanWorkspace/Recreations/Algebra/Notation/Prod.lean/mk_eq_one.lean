import Mathlib

variable {G H M N P R S : Type*}

variable [One M] [One N]

theorem mk_eq_one {x : M} {y : N} : (x, y) = 1 ↔ x = 1 ∧ y = 1 := mk_inj

