import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem closure_union (s t : Set R) : Subsemiring.closure (s ∪ t) = Subsemiring.closure s ⊔ Subsemiring.closure t := (Subsemiring.gi R).gc.l_sup

