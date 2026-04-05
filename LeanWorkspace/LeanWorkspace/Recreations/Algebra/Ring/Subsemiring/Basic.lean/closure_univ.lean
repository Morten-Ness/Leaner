import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem closure_univ : Subsemiring.closure (Set.univ : Set R) = ⊤ := @coe_top R _ ▸ Subsemiring.closure_eq ⊤

