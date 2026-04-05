import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem closure_insert_one (s : Set R) : Subsemiring.closure (insert 1 s) = Subsemiring.closure s := mod_cast Subsemiring.closure_insert_natCast 1 s

