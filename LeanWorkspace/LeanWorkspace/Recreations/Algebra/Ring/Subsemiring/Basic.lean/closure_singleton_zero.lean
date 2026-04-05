import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem closure_singleton_zero : Subsemiring.closure {(0 : R)} = ⊥ := mod_cast Subsemiring.closure_singleton_natCast 0

