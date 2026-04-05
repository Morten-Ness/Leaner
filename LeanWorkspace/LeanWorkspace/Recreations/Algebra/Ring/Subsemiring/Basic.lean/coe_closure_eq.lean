import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem coe_closure_eq (s : Set R) :
    (Subsemiring.closure s : Set R) = AddSubmonoid.closure (Submonoid.closure s : Set R) := by
  simp [← Submonoid.subsemiringClosure_toAddSubmonoid, Submonoid.subsemiringClosure_eq_closure]

