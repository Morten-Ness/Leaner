import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem closure_eq (s : Subsemiring R) : Subsemiring.closure (s : Set R) = s := (Subsemiring.gi R).l_u_eq s

