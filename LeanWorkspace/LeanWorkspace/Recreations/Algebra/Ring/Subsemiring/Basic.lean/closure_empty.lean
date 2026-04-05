import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem closure_empty : Subsemiring.closure (∅ : Set R) = ⊥ := (Subsemiring.gi R).gc.l_bot

