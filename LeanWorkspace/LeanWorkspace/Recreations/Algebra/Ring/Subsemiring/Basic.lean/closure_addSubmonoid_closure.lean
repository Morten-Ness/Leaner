import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem closure_addSubmonoid_closure {s : Set R} :
    Subsemiring.closure ↑(AddSubmonoid.closure s) = Subsemiring.closure s := by
  ext x
  refine ⟨fun hx => ?_, fun hx => Subsemiring.closure_mono AddSubmonoid.subset_closure hx⟩
  rintro - ⟨H, rfl⟩
  rintro - ⟨J, rfl⟩
  refine (AddSubmonoid.mem_closure.mp (Subsemiring.mem_closure_iff.mp hx)) H.toAddSubmonoid fun y hy => ?_
  refine (Submonoid.mem_closure.mp hy) H.toSubmonoid fun z hz => ?_
  exact (AddSubmonoid.mem_closure.mp hz) H.toAddSubmonoid fun w hw => J hw

