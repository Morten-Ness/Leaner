import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem mem_closure_iff {s : Set R} {x} :
    x ∈ Subsemiring.closure s ↔ x ∈ AddSubmonoid.closure (Submonoid.closure s : Set R) := Set.ext_iff.mp (Subsemiring.coe_closure_eq s) x

