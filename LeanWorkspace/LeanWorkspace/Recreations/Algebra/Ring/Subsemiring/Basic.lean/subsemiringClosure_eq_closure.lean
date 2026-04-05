import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem subsemiringClosure_eq_closure : M.subsemiringClosure = Subsemiring.closure (M : Set R) := by
  ext
  refine
    ⟨fun hx => ?_, fun hx =>
      (Subsemiring.mem_closure.mp hx) M.subsemiringClosure fun s sM => ?_⟩
  <;> rintro - ⟨H1, rfl⟩
  <;> rintro - ⟨H2, rfl⟩
  · exact AddSubmonoid.mem_closure.mp hx H1.toAddSubmonoid H2
  · exact H2 sM

