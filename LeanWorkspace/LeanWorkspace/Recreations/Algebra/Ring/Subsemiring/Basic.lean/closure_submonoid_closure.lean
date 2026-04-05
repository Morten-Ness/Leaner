import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem closure_submonoid_closure (s : Set R) : Subsemiring.closure ↑(Submonoid.closure s) = Subsemiring.closure s := le_antisymm
    (Subsemiring.closure_le.mpr fun _ hy =>
      (Submonoid.mem_closure.mp hy) (Subsemiring.closure s).toSubmonoid Subsemiring.subset_closure)
    (Subsemiring.closure_mono Submonoid.subset_closure)

