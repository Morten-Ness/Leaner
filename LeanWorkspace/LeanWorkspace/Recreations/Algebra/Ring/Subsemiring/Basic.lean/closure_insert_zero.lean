import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem closure_insert_zero (s : Set R) : Subsemiring.closure (insert 0 s) = Subsemiring.closure s := mod_cast Subsemiring.closure_insert_natCast 0 s

