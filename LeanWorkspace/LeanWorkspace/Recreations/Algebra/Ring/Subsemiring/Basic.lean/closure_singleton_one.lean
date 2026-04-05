import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem closure_singleton_one : Subsemiring.closure {(1 : R)} = ⊥ := mod_cast Subsemiring.closure_singleton_natCast 1

